# Publication Records

Successful publication writes one atomic JSON record in this directory. The
record binds archived full-review evidence and its checksum to the local image
ID, the explicit registry tag, and the immutable registry digest returned in
Docker `RepoDigests` after push.

Do not create a record by hand. Do not treat the local image ID as a registry
digest. Use a new record path for each publication attempt that should be
archived.
