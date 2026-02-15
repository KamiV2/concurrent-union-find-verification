# concurrent-union-find-verification
This repository contains the TLA+ files which verify the strong linearizability of the Jayanti-Tarjan randomized flipping algorithm for the UF problem, as well as various reductions to the UFS problem.

- `jtunionfind/` contains our verification that the randomized flipping concurrent union find algorithm due to Jayanti and Tarjan is strongly linearizable
- `uf/` contains our verification of a linearizable reduction from UF to UFS
- `ufid/` contains our verification of a strongly linearizable reduction from UF-id to UFS
