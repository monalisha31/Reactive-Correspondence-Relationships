# Screencast: Ecore → FHAS HUTN → ParticleWare → repaired model

**Video:** _<paste the link here once uploaded — e.g. YouTube (unlisted) or a
release asset>_

Duration: ~N minutes.

## What the screencast shows

1. **Start from the Ecore metamodel** (`../metamodels/Class.ecore`,
   `Relational.ecore`) — the source and target metamodels of the CD2RDBMS case.
2. **Convert to FHAS HUTN** — run the Ecore→FHAS conversion to obtain the deep,
   clade-structured HUTN representation ParticleWare consumes.
3. **Load into ParticleWare** together with the RCR package
   (`../packages/cd2rdbms.particle`).
4. **Apply the edit** — the `correctness1` rename `Person → Member`
   (`../models/correctness1/change.xmi`).
5. **Run the RCR synchronisation** — the reactive loop fires only the impacted
   witnesses and emits the local repairs.
6. **End result** — the materialised relational schema, which matches
   `../models/correctness1/expected1.xmi` (table, pivot, and key-column renamed;
   `firstName` and `Family` untouched).

> The full testbed source is not included in this artifact; the screencast
> demonstrates the executable behaviour end to end.
