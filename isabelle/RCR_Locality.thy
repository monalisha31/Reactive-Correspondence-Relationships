(*  Theory:  RCR_Locality
    Paper:   Reactive Correspondence Relationships for Incremental
             TGG-Style Model Synchronisation (SEFM 2026)

    Machine-checked spine of the formal development:
      - frame_locality                    frame locality
      - baseline_conformance              baseline local conformance
      - certificate_preservation          abstract certificate preservation
      - do_cop_preserves                  certificate-operation algebra: keep/insert/
                                          delete/replace preserve certificate validity
      - concrete_certificate_preservation lifts do_cop_preserves to a whole batch
      - repair_terminates                 termination via a multiset ranking

    Abstraction level (the honesty contract of the paper's mechanisation section):
      states are valuations of abstract locations; actions are abstract
      frame-respecting transformers.  Frame-respectingness of the concrete action
      algebra, local soundness of the concrete reactions, and the CD2RDBMS-specific
      choice of certificate operation are package obligations discharged outside
      Isabelle, validated by the executable runs.  The finite certificate-operation
      algebra itself is mechanised here: do_cop_preserves proves that
      keep/insert/delete/replace preserve certificate validity given valid new or
      replacement entries, and concrete_certificate_preservation lifts this to a
      whole batch, preserving certificate validity and the certificate/state
      "justifies" relation along any list of supported actions under two explicit
      residual hypotheses -- that each chosen operation inserts only valid entries
      (ins_ok/repl_ok) and that it preserves justifies (jpres) -- plus the cited
      Hermann et al. bridge from certificate validity to L(T) membership.

    Builds in Isabelle2025 with no "sorry"/"oops".
    Imports: Main + HOL-Library.Multiset.
*)

theory RCR_Locality
  imports Main "HOL-Library.Multiset"
begin

section \<open>Sect. 2.2: locations, states, conditions, actions\<close>

typedecl loc      \<comment> \<open>abstract locations: nodes, attribute slots, containment (Def. locations)\<close>
typedecl vl       \<comment> \<open>data universe, including the non-existence marker\<close>

type_synonym state = "loc \<Rightarrow> vl"   \<comment> \<open>valuation \<nu>\<close>

text \<open>A condition carries its declared read set and its satisfaction function.\<close>
record cond =
  rds :: "loc set"
  sat :: "state \<Rightarrow> bool"

text \<open>The Sect. 2.2 semantic commitment (Def. reads-foot): satisfaction is a
  function of the read locations and of nothing else.\<close>
definition reads_only :: "cond \<Rightarrow> bool" where
  "reads_only I \<longleftrightarrow>
     (\<forall>M M'. (\<forall>l \<in> rds I. M l = M' l) \<longrightarrow> sat I M = sat I M')"

text \<open>Abstract actions with declared write footprint (Def. reads-foot).\<close>
record act =
  foot :: "loc set"
  step :: "state \<Rightarrow> state"

definition frame_respecting :: "act \<Rightarrow> bool" where
  "frame_respecting a \<longleftrightarrow>
     (\<forall>M l. l \<notin> foot a \<longrightarrow> step a M l = M l)"

text \<open>Executing a finite batch of actions in order.\<close>
primrec exec :: "state \<Rightarrow> act list \<Rightarrow> state" where
  "exec M [] = M"
| "exec M (a # as) = exec (step a M) as"


section \<open>Sect. 4: RCR instances -- supp and rds live on the SAME carrier loc\<close>

record rcr =
  supp :: "loc set"
  cinv :: cond

text \<open>Def. support locality: the invariant reads only declared support.\<close>
definition supp_local :: "rcr \<Rightarrow> bool" where
  "supp_local r \<longleftrightarrow> rds (cinv r) \<subseteq> supp r"


section \<open>The RCR system locale: named assumptions = the paper's hypotheses\<close>

locale rcr_system =
  fixes R :: "rcr set"      \<comment> \<open>the package's RCR instances\<close>
    and A :: "act set"      \<comment> \<open>the supported actions (user edits and repairs)\<close>
  assumes wf_reads: "r \<in> R \<Longrightarrow> reads_only (cinv r)"
      \<comment> \<open>Sect. 2.2 satisfaction semantics\<close>
    and wf_supp:  "r \<in> R \<Longrightarrow> supp_local r"
      \<comment> \<open>Def. support locality (package well-formedness)\<close>
    and wf_frame: "a \<in> A \<Longrightarrow> frame_respecting a"
      \<comment> \<open>ASSUMED for the abstract semantics; discharged for the
          concrete action algebra in Sect. 7\<close>
begin

text \<open>Impact set (Sect. 4.2).\<close>
definition impact :: "act \<Rightarrow> rcr set" where
  "impact a = {r \<in> R. supp r \<inter> foot a \<noteq> {}}"

text \<open>Impact closure of a finite repair trace.\<close>
definition impact_closure :: "act list \<Rightarrow> rcr set" where
  "impact_closure tr = {r \<in> R. supp r \<inter> \<Union>(foot ` set tr) \<noteq> {}}"

text \<open>Baseline conformance predicate: every instance satisfies its
  TGG-induced local condition (identified with its invariant at this
  abstraction level).\<close>
definition conform :: "state \<Rightarrow> bool" where
  "conform M \<longleftrightarrow> (\<forall>r \<in> R. sat (cinv r) M)"

subsection \<open>THEOREM 1: Frame locality\<close>

theorem frame_locality:
  assumes rR: "r \<in> R"
      and aA: "a \<in> A"
      and disj: "supp r \<inter> foot a = {}"
  shows "sat (cinv r) M = sat (cinv r) (step a M)"
proof -
  have ro: "reads_only (cinv r)" by (rule wf_reads[OF rR])
  have sl: "rds (cinv r) \<subseteq> supp r"
    using wf_supp[OF rR] unfolding supp_local_def by simp
  have fr: "frame_respecting a" by (rule wf_frame[OF aA])
  have key: "\<forall>l \<in> rds (cinv r). M l = step a M l"
  proof
    fix l assume "l \<in> rds (cinv r)"
    with sl have "l \<in> supp r" by auto
    with disj have "l \<notin> foot a" by auto
    with fr show "M l = step a M l"
      unfolding frame_respecting_def by auto
  qed
  from ro key show ?thesis unfolding reads_only_def by blast
qed

corollary frame_locality_batch:
  assumes rR: "r \<in> R"
      and trA: "set tr \<subseteq> A"
      and disj: "supp r \<inter> \<Union>(foot ` set tr) = {}"
  shows "sat (cinv r) M = sat (cinv r) (exec M tr)"
  using trA disj
proof (induction tr arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have aA: "a \<in> A" and asA: "set as \<subseteq> A"
    using Cons.prems(1) by auto
  have d1: "supp r \<inter> foot a = {}"
   and d2: "supp r \<inter> \<Union>(foot ` set as) = {}"
    using Cons.prems(2) by auto
  have fl: "sat (cinv r) M = sat (cinv r) (step a M)"
    by (rule frame_locality[OF rR aA d1])
  have ih: "sat (cinv r) (step a M) = sat (cinv r) (exec (step a M) as)"
    by (rule Cons.IH[OF asA d2])
  from fl ih show ?case by simp
qed

subsection \<open>THEOREM 2: Baseline local conformance\<close>

text \<open>Def. 7 (locally sound reaction) + the fixpoint condition, at this
  abstraction level: a repair episode for an edit is a finite executed
  trace after which every instance in its impact closure satisfies its
  local condition.  That the concrete sync loop (event queue, reaction
  selection, guards) produces such traces is exactly the local-soundness
  + fixpoint obligation of Sect. 5.2, discharged per package (Sect. 7).\<close>
definition repair_complete :: "state \<Rightarrow> act list \<Rightarrow> bool" where
  "repair_complete M tr \<longleftrightarrow>
     (\<forall>r \<in> impact_closure tr. sat (cinv r) (exec M tr))"

theorem baseline_conformance:
  assumes trA: "set tr \<subseteq> A"
      and pre: "conform M"
      and rc: "repair_complete M tr"
  shows "conform (exec M tr)"
  unfolding conform_def
proof
  fix r assume rR: "r \<in> R"
  show "sat (cinv r) (exec M tr)"
  proof (cases "r \<in> impact_closure tr")
    case True
    then show ?thesis using rc unfolding repair_complete_def by blast
  next
    case False
    with rR have disj: "supp r \<inter> \<Union>(foot ` set tr) = {}"
      unfolding impact_closure_def by blast
    have "sat (cinv r) M = sat (cinv r) (exec M tr)"
      by (rule frame_locality_batch[OF rR trA disj])
    then show ?thesis using pre rR unfolding conform_def by blast
  qed
qed

end


section \<open>Sect. 5.3: certificates -- Def. 9 unbundled into named assumptions\<close>

text \<open>Certificates are abstract.  @{text valid} is certificate validity;
  @{text justifies} relates a certificate to the state it derives;
  @{text in_lang} is membership of the projected state in the TGG
  consistency language.  Each component of the paper's Def. 9
  (certificate-admissible package) becomes a separate, named locale
  assumption, so the theorem shows exactly which combination yields
  preservation.

  NOT mechanized (paper / Sect. 7 obligations): that the concrete
  CD2RDBMS reactions realise @{text ctrans}; that @{text valid} +
  @{text justifies} characterise derivability in the concrete TGG;
  confluence/policy for the loop's choice among reactions; termination
  (executions are finite batches by construction; Sect. 5.4 supplies
  the argument that the loop produces them).\<close>

locale certified_system = rcr_system +
  fixes valid     :: "'c \<Rightarrow> bool"
    and ctrans    :: "act \<Rightarrow> 'c \<Rightarrow> 'c"      \<comment> \<open>certificate transformer (Def. 9, part 1)\<close>
    and justifies :: "'c \<Rightarrow> state \<Rightarrow> bool"
    and in_lang   :: "state \<Rightarrow> bool"
  assumes ctrans_preserves:
    "\<lbrakk> a \<in> A; valid c; justifies c M \<rbrakk>
       \<Longrightarrow> valid (ctrans a c) \<and> justifies (ctrans a c) (step a M)"
      \<comment> \<open>creation, deletion (via before-images), and structural repair
          transform valid certificates into valid certificates\<close>
    and cert_sound:
    "\<lbrakk> valid c; justifies c M \<rbrakk> \<Longrightarrow> in_lang M"
      \<comment> \<open>a valid certificate witnesses TGG-language membership\<close>
begin

primrec cexec :: "'c \<Rightarrow> act list \<Rightarrow> 'c" where
  "cexec c [] = c"
| "cexec c (a # as) = cexec (ctrans a c) as"

subsection \<open>THEOREM 3: Certified TGG-language preservation\<close>

theorem certificate_preservation:
  assumes "set as \<subseteq> A"
      and "valid c"
      and "justifies c M"
  shows "valid (cexec c as)
       \<and> justifies (cexec c as) (exec M as)
       \<and> in_lang (exec M as)"
  using assms
proof (induction as arbitrary: c M)
  case Nil
  then have "in_lang M" using cert_sound by blast
  with Nil show ?case by simp
next
  case (Cons a as)
  have aA: "a \<in> A" and asA: "set as \<subseteq> A"
    using Cons.prems(1) by auto
  have step1: "valid (ctrans a c) \<and> justifies (ctrans a c) (step a M)"
    by (rule ctrans_preserves[OF aA Cons.prems(2) Cons.prems(3)])
  then have v: "valid (ctrans a c)"
        and j: "justifies (ctrans a c) (step a M)" by auto
  show ?case using Cons.IH[OF asA v j] by simp
qed

end


section \<open>Concrete certificate model (discharges the transformer obligation)\<close>

text \<open>The abstract theorem above assumes a certificate transformer that
  preserves validity (\<open>ctrans_preserves\<close>).  Here we exhibit a concrete
  certificate representation and prove that preservation as a lemma, by the
  same four-case analysis the paper gives for Theorem~3.  Only the bridge from
  certificate validity to TGG-language membership remains a cited assumption
  (Hermann et al.).\<close>

datatype rid = RClassTable | RAttrCol | RAttrPivot | RModelScope
  \<comment> \<open>rule ids matching the package's RCR types (ClassTable, AttrCol, AttrPivot, ModelScope)\<close>

datatype centry = CEntry rid "loc set"   \<comment> \<open>a recorded rule application and its participants\<close>

type_synonym ccert = "centry set"

definition ccvalid :: "(centry \<Rightarrow> bool) \<Rightarrow> ccert \<Rightarrow> bool" where
  "ccvalid ok c \<longleftrightarrow> (\<forall>e \<in> c. ok e)"

text \<open>The four certificate operations: value repair keeps the certificate,
  creation inserts an entry, deletion removes entries (via a before-image),
  and structural replace retires entries and inserts a replacement.\<close>
datatype cop = Keep | Ins centry | Del "centry set" | Repl "centry set" centry

primrec do_cop :: "cop \<Rightarrow> ccert \<Rightarrow> ccert" where
  "do_cop Keep c = c"
| "do_cop (Ins e) c = insert e c"
| "do_cop (Del E) c = c - E"
| "do_cop (Repl E e) c = insert e (c - E)"

text \<open>Each operation preserves validity, given that any newly recorded entry
  is itself valid.  This is the case analysis the paper previously stated only
  as a proof sketch.\<close>
lemma do_cop_preserves:
  assumes "ccvalid ok c"
      and "\<And>e. op = Ins e \<Longrightarrow> ok e"
      and "\<And>E e. op = Repl E e \<Longrightarrow> ok e"
  shows "ccvalid ok (do_cop op c)"
  using assms by (cases op) (auto simp: ccvalid_def)


section \<open>Wiring do_cop into a batch-level certificate-preservation result\<close>

text \<open>The abstract theorem certificate_preservation (locale certified_system)
  is proved under the assumption ctrans_preserves, which bundles two facts about
  the certificate transformer: preservation of certificate validity, and
  preservation of a certificate/state justifies relation.  Previously
  do_cop_preserves stood to one side of that theorem.  Here we connect them:
  for the concrete do_cop transformer we prove, by the same induction as
  Theorem 3, that BOTH validity and the justifies relation are preserved along
  an arbitrary batch of supported actions.  The discharge of the validity step
  is exactly do_cop_preserves.  Two residual obligations are made explicit as
  hypotheses, and are precisely the package/testbed obligations discussed in the
  paper: that the operation chosen for each action only inserts valid certificate
  entries (ins_ok, repl_ok), and that it preserves justifies (jpres).  The bridge
  from certificate validity to membership in the concrete TGG language L(T)
  remains the cited Hermann et al. result.\<close>

primrec cexec0 :: "(act \<Rightarrow> cop) \<Rightarrow> ccert \<Rightarrow> act list \<Rightarrow> ccert" where
  "cexec0 sel c [] = c"
| "cexec0 sel c (a # as) = cexec0 sel (do_cop (sel a) c) as"

context rcr_system
begin

theorem concrete_certificate_preservation:
  fixes ok   :: "centry \<Rightarrow> bool"
    and sel  :: "act \<Rightarrow> cop"
    and just :: "ccert \<Rightarrow> state \<Rightarrow> bool"
  assumes ins_ok:  "\<And>a e.   a \<in> A \<Longrightarrow> sel a = Ins e    \<Longrightarrow> ok e"
      and repl_ok: "\<And>a E e. a \<in> A \<Longrightarrow> sel a = Repl E e \<Longrightarrow> ok e"
      and jpres:   "\<And>a c M. a \<in> A \<Longrightarrow> just c M \<Longrightarrow> just (do_cop (sel a) c) (step a M)"
      and asA:     "set as \<subseteq> A"
      and cval:    "ccvalid ok c"
      and j0:      "just c M"
    shows "ccvalid ok (cexec0 sel c as) \<and> just (cexec0 sel c as) (exec M as)"
  using asA cval j0
proof (induction as arbitrary: c M)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  have aA: "a \<in> A" and asA': "set as \<subseteq> A"
    using Cons.prems(1) by auto
  have v1: "ccvalid ok (do_cop (sel a) c)"
  proof (rule do_cop_preserves[OF Cons.prems(2)])
    fix e assume "sel a = Ins e"
    then show "ok e" using ins_ok[OF aA] by blast
  next
    fix E e assume "sel a = Repl E e"
    then show "ok e" using repl_ok[OF aA] by blast
  qed
  have j1: "just (do_cop (sel a) c) (step a M)"
    using jpres[OF aA Cons.prems(3)] .
  from Cons.IH[OF asA' v1 j1]
  show ?case by simp
qed

end


section \<open>Sect. 6.4: termination of the repair loop via a multiset ranking\<close>

text \<open>A repair episode is abstracted to its effect on the multiset of ranks of
  currently-violated witnesses (Def. repair-dependency graph and rank).  By local
  soundness a productive step repairs one witness, removing one occurrence of its
  rank @{term k}; by repair-acyclicity every OTHER witness it newly invalidates has
  a strictly smaller rank.  Such a step is exactly a descent in the
  Dershowitz--Manna multiset order over the naturals, which is well founded, so no
  infinite repair episode exists.  That the concrete synchronisation loop's
  productive steps realise repair_step is the per-package obligation
  discharged in Sect. 7.\<close>

definition repair_step :: "nat multiset \<Rightarrow> nat multiset \<Rightarrow> bool" where
  "repair_step M' M \<longleftrightarrow>
     (\<exists>k N. k \<in># M \<and> (\<forall>x. x \<in># N \<longrightarrow> x < k) \<and> M' = (M - {#k#}) + N)"

lemma repair_step_imp_mult:
  assumes "repair_step M' M"
  shows "(M', M) \<in> mult {(x, y). x < (y::nat)}"
proof -
  from assms obtain k N
    where k: "k \<in># M"
      and N: "\<forall>x. x \<in># N \<longrightarrow> x < k"
      and M': "M' = (M - {#k#}) + N"
    unfolding repair_step_def by blast
  have split: "M = (M - {#k#}) + {#k#}" using k by simp
  have "((M - {#k#}) + N, (M - {#k#}) + {#k#}) \<in> mult {(x, y). x < (y::nat)}"
    by (rule one_step_implies_mult) (use N in auto)
  thus ?thesis using M' split by simp
qed

theorem repair_terminates:
  "wf {(M', M). repair_step M' M}"
proof (rule wf_subset)
  show "wf (mult {(x, y). x < (y::nat)})"
  proof (rule wf_mult)
    have "{(x, y). x < (y::nat)} = less_than" by (auto simp: less_than_iff)
    thus "wf {(x, y). x < (y::nat)}" by (simp add: wf_less_than)
  qed
  show "{(M', M). repair_step M' M} \<subseteq> mult {(x, y). x < (y::nat)}"
    using repair_step_imp_mult by blast
qed

end
