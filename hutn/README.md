# HUTN (FHAS) inputs

ParticleWare consumes models in the **FHAS HUTN** representation (a deep,
clade-structured textual encoding: `EN`/`CA`/`RE`/`PA` nodes for entities,
classifications, relationships, and participations).

The FHAS HUTN file used for a run is **produced from the Ecore metamodel** in
`../metamodels/` by the Ecore→FHAS conversion step. The screencast in `../demo/`
shows this conversion and the subsequent ParticleWare run.

Drop the generated `*_FHAS_*.hutn` file here to keep a run self-contained.
