This repo is aiming to formalize the bread and butter of matroid theory in lean4.
The goal is eventually to have is all included in the lean4 math library : 
https://github.com/leanprover-community/mathlib4

Experimental : the following link should give an auto-updating repo-specific documentation page: 
https://apnelson1.github.io/Matroid/docs

At the time of writing, the contents of this repo are being submitted to mathlib piece by piece.
Currently already in mathlib are : 

* The definition of a matroid in terms of the base axioms : Mathlib/Data/Matroid/Basic
* Construction of matroids in terms of independence axioms : Mathlib/Data/Matroid/IndepAxioms
* Matroid duality : Mathlib/Data/Matroid/Dual
* Restricting a matroid to a set, and the restriction order : Mathlib/Data/Matroid/Restrict
* Matroids with at most one base : Mathlib/Data/Matroid/Constructions
* Maps and comaps between matroids : Matroid/Map
* Matroid closure : Mathlib/Data/Matroid/Closure
* Matroid circuits : Mathlib/Data/Matroid/Circuit
* Cardinal-valued matroid rank : Mathlib/Data/Matroid/Rank/Cardinal
* Finite-rank sets : Mathlib/Data/Matroid/Rank/Finite
* Direct sums : Mathlib/Data/Matroid/Sum

Topics in this repo are listed below. 

* Isomorphism : Matroid/Equiv
* Circuits and cocircuits : Matroid/IsCircuit
* Loops : Matroid/Loop
* The rank function : Matroid/Rank/*
* Minors : Matroid/Minor/Basic and Matroid/Minor/Iso
* Relative Rank : Matroid/Minor/Rank
* Flats, Hyperplanes, Covers : Matroid/Flat/*
* Truncations : Matroid/Constructions/Truncate
* Parallel elements : Matroid/Parallel
* Parallel and series extension : Matroid/Constructions/ParallelExtension
* Simplicity and simplification : Matroid/Simple
* Modular sets, matroids, pairs and families : Matroid/Modular/*
* Modular cuts, extensions and projections : Matroid/Extension
* Circuit-hyperplane relaxation : Matroid/Constructions/Relax
* Paving matroids : Matroid/Paving
* The matroid intersection theorem : Matroid/Intersection
* Uniform matroids (finite and infinite) : Matroid/Uniform
* Connectivity, local connectivity, skewness and connectivity between sets : Matroid/Connectivity/*
* Cryptomorphism for flats, circuits, closure and rank : Matroid/Axioms/*
* Quotients and the weak order : Matroid/Order/*
* Representability : Matroid/Representation/*
* Circuit/cocircuit intersections : Matroid/Binary/Crossing
* Tutte's excluded minor theorem for finitary binary matroids : Matroid/Binary/Representation

If you have any feature requests or thoughts, please contact me at apnelson@uwaterloo.ca - 
I am more than happy to see others make use of this code!
