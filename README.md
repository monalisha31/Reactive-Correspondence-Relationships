# Reactive Correspondence Relationships — Artifact

Replication artifact for the paper:

> **Reactive Correspondence Relationships for Incremental TGG-Style Model
> Synchronisation** (SEFM 2026)

Reactive Correspondence Relationships (RCRs) turn TGG-style correspondences from
passive witnesses into local synchronisation controllers: each correspondence
carries a local invariant, repair reactions, provenance, and a certificate mode,
and reacts to edits by emitting model-level repair actions
(`Change` / `Add` / `Delete` / `Batch`) that drive the integrated state back to a
fixpoint without a global rerun.

This artifact contains (a) the **machine-checked Isabelle/HOL theory** behind the
formal results, and (b) the **modelling inputs** for the TTC 2023
class-to-relational (CD2RDBMS) case study, including the verified `correctness1`
rename scenario. A short **screencast** demonstrates the end-to-end pipeline
(Ecore → FHAS HUTN → ParticleWare → repaired relational model).

---

## Contents

```
rcr-artifact/
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
│       └── cd2rdbms_rename_input.hutn   ready-to-run input: Source + Target + the
│                                        user edit (no Corr — auto-derived at runtime)
├── packages/
│   └── scenarios/
│       ├── 01_create_factory.particle       Create  (ModelScopeRCR factory)
│       ├── 02_change_rename.particle         Change  (rename cascade; the demo package)
│       ├── 03_delete_attribute.particle      Delete  (before-image retire)
│       └── 04_batch_single_to_multi.particle Batch   (structural replace)
├── hutn/
│   └── README.md               how the FHAS HUTN input is produced (see demo)
└── demo/
    └── README.md               screencast: link + what it shows
```

## Quickstart: run the rename in the ParticleWare UI

1. Start the web app and open `http://localhost:8181/workspace.xhtml` → **Particle pipeline**.
2. Load model `models/rename-demo/cd2rdbms_rename_input.hutn` and package
   `packages/scenarios/02_change_rename.particle`.
3. Run. The runtime **auto-derives** the RCR instances from source+target (no `Corr`
   clade is shipped), reads the single `Change Person.name → Member` event, and emits
   the three local repairs (table, pivot, and `personId → memberId`), ending in the
   materialised relational schema. The four packages in `packages/scenarios/`
   correspond one-to-one to the Create / Change / Delete / Batch listings in the paper.

---

## 1. Machine-checked theory (`isabelle/RCR_Locality.thy`)

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
*outside* Isabelle and validated by the executable runs below.

---

## 2. CD2RDBMS case study (modelling inputs)

The `metamodels/` and `models/correctness1/` files are the TTC 2023 incremental
class-to-relational benchmark inputs (provenance in `metamodels/README.md`). The
RCR package in `packages/cd2rdbms.particle` declares the four correspondence
types used in the paper:

- `ClassTableRCR` — class ↔ table (`table.name = class.name`)
- `AttrColRCR` — single-valued attribute ↔ column (`col.name = attr.name`)
- `AttrPivotRCR` — multi-valued attribute ↔ pivot table (n-ary; the owning class
  is a **context role**, driving `pivot.name` and the `…Id` key column)
- `ModelScopeRCR` — a factory over the roots that creates witnesses on `Add`

**Verified result (`correctness1`).** Renaming `Person → Member` triggers three
local repairs to a fixpoint — the table `Person → Member`, the pivot table
`Person_emailAddresses → Member_emailAddresses`, and its key column
`personId → memberId` — while `firstName` and `Family` are left untouched. The
materialised schema matches `models/correctness1/expected1.xmi` table-for-table
and column-for-column.

---

## 3. Demo

`demo/README.md` links a short screencast showing the full pipeline end to end,
starting from an Ecore metamodel, converting it to the FHAS HUTN representation,
loading it into ParticleWare, and running the RCR synchronisation to the repaired
relational model.

---

## How to cite

If you use this artifact, please cite the SEFM 2026 paper (see the paper for the
full reference).

## License

See `LICENSE`.
