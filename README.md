# Reactive Correspondence Relationships — Results

Supporting **results and material** for the paper:

> **Reactive Correspondence Relationships for Incremental TGG-Style Model
> Synchronisation** (SEFM 2026)

This repository is **not a turnkey replication package**. It collects the concrete
results behind the paper's claims: the machine-checked Isabelle/HOL development,
the modelling inputs and outputs of the class-to-relational case study, the RCR
packages for each edit scenario, and a screen recording of the prototype running
the rename scenario in the PAMoLA / ParticleWare workspace.

Reactive Correspondence Relationships (RCRs) turn TGG-style correspondences from
passive witnesses into local synchronisation controllers: each correspondence
carries a local invariant, repair reactions, provenance, and a certificate mode,
and reacts to edits by emitting model-level repair actions
(`Change` / `Add` / `Delete` / `Batch`) that drive the integrated state back to a
fixpoint without a global rerun.

---

## Contents

```
.
├── isabelle/
│   └── RCR_Locality.thy        Isabelle/HOL development (the proof of record)
├── metamodels/
│   ├── Class.ecore             source metamodel (class diagrams)
│   ├── Relational.ecore        target metamodel (relational schemas)
│   ├── Changes.ecore           edit/change metamodel
│   └── README.md               provenance vs. the ATL Zoo Class2Relational
├── models/
│   ├── correctness1/
│   │   ├── class.xmi           input class model (before the edit)
│   │   ├── change.xmi          the rename edit (Person → Member)
│   │   └── expected1.xmi       expected relational schema after repair
│   └── rename-demo/
│       └── cd2rdbms_rename_input.hutn   the model loaded in the demo:
│                                        Source + Target + the user edit
│                                        (no Corr — correspondences are derived at runtime)
├── packages/
│   └── scenarios/
│       ├── 01_create_factory.particle       Create  (ModelScopeRCR factory)
│       ├── 02_change_rename.particle         Change  (rename cascade; the demo package)
│       ├── 03_delete_attribute.particle      Delete  (before-image retire)
│       └── 04_batch_single_to_multi.particle Batch   (structural replace)
└── demo/
    ├── PAMoLA_Workspace_demo.mp4   screen recording of the rename run (see below)
    └── README.md
```

---

## 1. Demo recording (`demo/PAMoLA_Workspace_demo.mp4`)

The video records the prototype running the paper's **rename scenario** live in the
PAMoLA / ParticleWare web workspace. It shows the full incremental-synchronisation
loop on screen:

1. **Load the input model** — `models/rename-demo/cd2rdbms_rename_input.hutn`, which
   contains only the **Source** class model, the **Target** relational schema, and a
   single user **edit event** (`Change Person.name → Member`). No correspondences are
   shipped in the file.
2. **Load the RCR package** — `packages/scenarios/02_change_rename.particle`.
3. **Auto-derivation** — because the model has no `Corr` clade, the runtime synthesises
   the RCR instances (`ctr_Person`, `apr_Person_emails`, …) by pairing source and target
   elements of matching declared types.
4. **Reactive repair** — the runtime reads the edit event and fires the repair reactions,
   emitting the three local repairs:
   - the table `Person → Member`,
   - the pivot table `Person_emailAddresses → Member_emailAddresses`,
   - and its key column `personId → memberId`,

   while `firstName` and `Family` stay untouched.
5. **Result** — the materialised relational schema, reached at a local fixpoint without a
   global rerun. It matches `models/correctness1/expected1.xmi` table-for-table and
   column-for-column.

The four packages under `packages/scenarios/` correspond one-to-one to the
Create / Change / Delete / Batch listings in the paper.

---

## 2. Machine-checked theory (`isabelle/RCR_Locality.thy`)

The theory mechanises the abstract spine of the paper's formal results:

| Lemma / theorem in the theory      | Paper result                          |
|------------------------------------|---------------------------------------|
| `frame_locality`                   | Frame locality                        |
| `baseline_conformance`             | Baseline local conformance (lifting)  |
| `certificate_preservation`         | Abstract certificate preservation     |
| `do_cop_preserves`                 | Certificate-operation algebra preserves validity |
| `concrete_certificate_preservation`| Lifts the above to whole repair batches |
| `repair_terminates`                | Termination (multiset ranking)        |

**Requirements.** [Isabelle2025](https://isabelle.in.tum.de/) (no AFP entries
required; imports only `Main` and `HOL-Library.Multiset`).

**Check it.**
1. Open `isabelle/RCR_Locality.thy` in Isabelle/jEdit.
2. Press `Ctrl+End` to force-process the whole theory.
3. The Theories panel turns fully green with no errors; the development contains
   no `sorry` or `oops`.

What is **mechanised** vs. **validated by runs** vs. **assumed** is documented in
the theory header and in the paper's mechanisation section (the honesty contract):
package-specific obligations (frame-respectingness, local soundness, the correct
certificate-operation choice, the certificate-to-language bridge) are discharged
*outside* Isabelle and validated by the executable runs shown in the demo.

---

## 3. Class-to-relational case study (CD2RDBMS)

The `metamodels/` and `models/correctness1/` files are the TTC 2023 incremental
class-to-relational benchmark inputs (provenance in `metamodels/README.md`). The
RCR packages declare the correspondence types used in the paper:

- `ClassTableRCR` — class ↔ table (`table.name = class.name`)
- `AttrColRCR` — single-valued attribute ↔ column (`col.name = attr.name`)
- `AttrPivotRCR` — multi-valued attribute ↔ pivot table (n-ary; the owning class
  is a **context role**, driving `pivot.name` and the `…Id` key column)
- `ModelScopeRCR` — a factory over the roots that creates witnesses on `Add`

The verified `correctness1` result is the rename shown in the demo: its materialised
schema matches `models/correctness1/expected1.xmi`.

---

## How to cite

If you use this material, please cite the SEFM 2026 paper (see the paper for the
full reference).

## License

See `LICENSE`.
