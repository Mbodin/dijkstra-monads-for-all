Note: This is a clone of [this repository](https://gitlab.inria.fr/kmaillar/dijkstra-monads-for-all).
You may prefer checking the original first.

# Dijkstra Monads for All

Coq development for the paper:
- Kenji Maillard, Danel Ahman, Robert Atkey, Guido Martinez,
  Cătălin Hriţcu, Exequiel Rivas, and Éric Tanter.
  **[Dijkstra Monads for All](https://arxiv.org/abs/1903.01237)**.
  arXiv:1903.01237. March, 2019.


# Prerequisites

This development requires `esy`.
It can be installed through:
```bash
npm install --global esy@latest
```

# Step-by-step Guide

Run `esy` from this directory to compile all the coq files
(this step is needed for the walkthrough). It should succeed
displaying only warnings and coq terms.

The file `theories/README.v` provides a step-by-step walkthrough
that maps the claims of the paper to parts of the Coq development.

The best way to follow along is to go through this file with emacs
within the `esy` environment.  This can be done by typing `esy emacs`
followed by the wanted file name.
(emacs and Proof General are installed in our Docker image)


# Organisation of the directories

- theories/          : root of all the Coq files
- theories/sprop     : development of Dijkstra monads using SProp
- theories/SRelation : adaptation of part of the standard library to SProp
- theories/SM        : SM language and denotations


# Content of the files

## In theories/

* theories/Base.v:
  basic definitions not present in the standard library
  
* theories/README.v:
  walkthrough of the paper, pointing out the relevant definitions and examples
  
* theories/dijkstra_updated.v
  POC of extensions to the paper presented for rebuttal


## In theories/sprop/

* theories/sprop/SPropBase.v
  Basic constructions on sprop
  
* theories/sprop/WellFounded.v
  Construction of well-founded orders
  
* theories/sprop/SPropMonadicStructures.v:
  monad like structures (Dijkstra monads...)

* theories/sprop/Monoid.v
  monoids and monoid actions

* theories/sprop/DirectedContainers.v
  directed containers in order to define dependent update monads

* theories/sprop/MonadExamples.v
  Examples of monads (state, exception, list, free monads...)

* theories/sprop/SpecificationMonads.v
  Examples of specification monads

* theories/sprop/DijkstraMonadExamples.v
  Examples of Dijkstra monads 

## In theories/SM/

* theories/SM/dlist.v:
  implementation of list indexed-list

* theories/SM/SMSyntax.v:
  syntax of SM

* theories/SM/SMDenotations.v
  Definition of the denotation and logical relation

* theories/SM/MonadTransformer.v
  Provide the components of a (plain) monad transformer
  from a monad definition in SM under suitable hypothesis.

* theories/SM/SMDenotationsMonotonic.v
  Definition of the ordered denotation and logical relation

* theories/SM/MonadTransformer.v
  Provide the components of an ordered monad transformer
  from a monad definition in SM under suitable hypothesis.

* theories/SM/MonadTransformerMonotonic.v
  Provide the components of an ordered monad transformer
  from a monad definition in SM under suitable hypothesis.

* theories/SM/SMMonadExamples.v
  Example of a monad internal to SM translated to a monad transformer


# Axioms and assumptions

Most of the development uses the recent SProp feature of Coq (instead of relying on UIP axiom).

The functional extensionality axiom from Coq's standard library is used
extensively in the development, as well as two variations of it with 
respect to SProp (that can be found in `theories/sprop/SPropBase.v`, module `SPropAxioms`). 
This module also defines the axiom of propositional extensionality 
for strict propositions.

The use of these axioms can be checked for instance at the end of 
`theories/README.v` using `Print Assumptions term.`.

As mentioned in Section 7 of the paper, "the mechanized version of
Theorem 2 thus assumes a semantic hypothesis requiring that the
denotation of bind is homomorphic, and under this assumption derives
the full monad transformer (including all the laws) in Coq."

No proof in the developement is admitted.

# F* development

There is also an F* development for this paper at:
https://github.com/FStarLang/FStar/tree/guido_effects/examples/dm4all
