This repo is aiming to formalize the bread and butter of matroid theory in lean4.
The goal is eventually to have is all included in the lean4 math library : 
https://github.com/leanprover-community/mathlib4


At the time of writing, a few files originally here have been transferred to 
mathlib: these are

* The definition of a matroid in terms of the base axioms : Mathlib/Data/Matroid/Basic
* Construction of matroids in terms of independence axioms : Mathlib/Data/Matroid/IndepAxioms
* Matroid duality : Mathlib/Data/Matroid/Dual
* Restricting a matroid to a set, and the restriction order : Mathlib/Data/Matroid/Restrict

Topics in this repo are listed below. 

* Free and co-free matroids : Matroid/Constructions/Basic
* Isomorphism : Matroid/Equiv
* Maps and comaps between matroids : Matroid/Map
* Direct sums : Matroid/Constructions/DirectSum
* The closure function : Matroid/Closure
* Circuits and cocircuits : Matroid/Circuit
* Loops : Matroid/Loop
* The rank function : Matroid/Rank
* Minors : Matroid/Minor/Basic and Matroid/Minor/Iso
* Relative Rank : Matroid/Minor/Rank
* Flats : Matroid/Flat
* Truncations : Matroid/Constructions/Truncate
* Simplicity and simplification : Matroid/Simple
* Modular sets, pairs and families : Matroid/Modular
* Modular cuts, extensions and projections : Matroid/Extension
* Circuit-hyperplane relaxation : Matroid/Relax
* Paving matroids : Matroid/Paving
* The matroid intersection theorem : Matroid/Intersection

The following currently need a few fixes to work correctly. 
* Uniform matroids : Matroid/Uniform
* Transversal matroids : Matroid/Transversal
* Parallel and series extensions : Matroid/ParallelExtension
* Matroid invariants and minor-closed properties : Matroid/Class
* Representability : Matroid/Representation/* 
  (Some of this requires a fair amount of linear algebra stuff to be added to mathlib to work - see Matroid/ForMathlib)

  


Additionally, there is some material from an earlier lean3 version of the repo 
which is essentially done but needs to be ported. This includes

- Kung's theorem on excluding a line minor
- quotients/projections
