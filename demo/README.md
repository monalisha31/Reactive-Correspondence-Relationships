# Demo recording

**`PAMoLA_Workspace_demo.mp4`** — screen recording of the prototype running the
paper's rename scenario in the PAMoLA / ParticleWare web workspace.

## What it shows

1. **Load the input model** `../models/rename-demo/cd2rdbms_rename_input.hutn` —
   Source class model + Target relational schema + one user edit
   (`Change Person.name → Member`). No correspondences are shipped in the file.
2. **Load the RCR package** `../packages/scenarios/02_change_rename.particle`.
3. **Auto-derivation** — with no `Corr` clade present, the runtime synthesises the
   RCR instances by pairing source/target elements of matching declared types.
4. **Reactive repair** — the runtime reads the edit and fires the repair reactions,
   producing three local repairs: the table `Person → Member`, the pivot table
   `Person_emailAddresses → Member_emailAddresses`, and its key column
   `personId → memberId`; `firstName` and `Family` stay untouched.
5. **Result** — the materialised relational schema at a local fixpoint, matching
   `../models/correctness1/expected1.xmi`.
