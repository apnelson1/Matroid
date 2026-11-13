# Verification commands

Run these commands from the repository root:

```sh
lake build Matroid
lake test
```

The registered regression suite includes JCT consumers, prerequisite and generality tests,
polygonal construction tests, and selected axiom-dependency checks. To build those consumers
individually:

```sh
lake build MatroidTests.JCTGenerality MatroidTests.JordanCurve \
  MatroidTests.JordanPrerequisites MatroidTests.ConstructionTopology \
  MatroidTests.ConstructionPolygonal MatroidTests.ConstructionSubdivision
```

[Generality consumers](../../../tests/MatroidTests/JCTGenerality.lean) exercise algebraic figures,
closed-set segment cutting, nonsimple polygonal access, local component parametrization,
compact circuit extraction, homotopy retracts, frontier transport, and real normed planes.

These commands check compilation and the assertions embedded in the registered tests. The
former specialized scripts for import boundaries, retired interfaces, and broader JCT axiom
inventories have been removed; those additional checks are no longer supplied by these commands.

The `Unfinished` archive preserves statements with proof holes and historical source that may
fail to compile. It is not registered as a Lake library or included in the default build.
Successful compilation of its contracts would establish well-formedness, not mathematical truth.
