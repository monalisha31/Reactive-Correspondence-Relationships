theory RCR_Locality
  imports Main "HOL-Library.Multiset"
begin

section \<open>Sect. 2.2: locations, states, conditions, actions\<close>

typedecl loc
typedecl vl

type_synonym state = "loc \<Rightarrow> vl"

record cond =
  rds :: "loc set"
  sat :: "state \<Rightarrow> bool"

definition reads_only :: "cond \<Rightarrow> bool" where
  "reads_only I \<longleftrightarrow>
     (\<forall>M M'. (\<forall>l \<in> rds I. M l = M' l) \<longrightarrow> sat I M = sat I M')"

record act =
  foot :: "loc set"
  step :: "state \<Rightarrow> state"

definition frame_respecting :: "act \<Rightarrow> bool" where
  "frame_respecting a \<longleftrightarrow>
     (\<forall>M l. l \<notin> foot a \<longrightarrow> step a M l = M l)"

primrec exec :: "state \<Rightarrow> act list \<Rightarrow> state" where
  "exec M [] = M"
| "exec M (a # as) = exec (step a M) as"

section \<open>Sect. 4: RCR instances -- supp and rds live on the SAME carrier loc\<close>

record rcr =
  supp :: "loc set"
  cinv :: cond

definition supp_local :: "rcr \<Rightarrow> bool" where
  "supp_local r \<longleftrightarrow> rds (cinv r) \<subseteq> supp r"

section \<open>The RCR system locale: named assumptions = the paper's hypotheses\<close>

locale rcr_system =
  fixes R :: "rcr set"
    and A :: "act set"
  assumes wf_reads: "r \<in> R \<Longrightarrow> reads_only (cinv r)"

    and wf_supp:  "r \<in> R \<Longrightarrow> supp_local r"

    and wf_frame: "a \<in> A \<Longrightarrow> frame_respecting a"

begin

definition impact :: "act \<Rightarrow> rcr set" where
  "impact a = {r \<in> R. supp r \<inter> foot a \<noteq> {}}"

definition impact_closure :: "act list \<Rightarrow> rcr set" where
  "impact_closure tr = {r \<in> R. supp r \<inter> \<Union>(foot ` set tr) \<noteq> {}}"

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

locale certified_system = rcr_system +
  fixes valid     :: "'c \<Rightarrow> bool"
    and ctrans    :: "act \<Rightarrow> 'c \<Rightarrow> 'c"
    and justifies :: "'c \<Rightarrow> state \<Rightarrow> bool"
    and in_lang   :: "state \<Rightarrow> bool"
  assumes ctrans_preserves:
    "\<lbrakk> a \<in> A; valid c; justifies c M \<rbrakk>
       \<Longrightarrow> valid (ctrans a c) \<and> justifies (ctrans a c) (step a M)"

    and cert_sound:
    "\<lbrakk> valid c; justifies c M \<rbrakk> \<Longrightarrow> in_lang M"

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


datatype rid = RClassTable | RAttrCol | RAttrPivot | RModelScope

datatype centry = CEntry rid "loc set"

type_synonym ccert = "centry set"

definition ccvalid :: "(centry \<Rightarrow> bool) \<Rightarrow> ccert \<Rightarrow> bool" where
  "ccvalid ok c \<longleftrightarrow> (\<forall>e \<in> c. ok e)"

datatype cop = Keep | Ins centry | Del "centry set" | Repl "centry set" centry

primrec do_cop :: "cop \<Rightarrow> ccert \<Rightarrow> ccert" where
  "do_cop Keep c = c"
| "do_cop (Ins e) c = insert e c"
| "do_cop (Del E) c = c - E"
| "do_cop (Repl E e) c = insert e (c - E)"

lemma do_cop_preserves:
  assumes "ccvalid ok c"
      and "\<And>e. op = Ins e \<Longrightarrow> ok e"
      and "\<And>E e. op = Repl E e \<Longrightarrow> ok e"
  shows "ccvalid ok (do_cop op c)"
  using assms by (cases op) (auto simp: ccvalid_def)

section \<open>Wiring do_cop into a batch-level certificate-preservation result\<close>

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
