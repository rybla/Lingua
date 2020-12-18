# README

Implementations of and reasonings about the following languages:

| name | description | common parlence | resources |
| --- | --- | --- | --- |
| [λ][λ] | simply-typed λ-calculus | STλC |
| [λ2][λ2] | λ with type polymorphism | System F |
| [λω][λω] | λ2 with type constructors | System Fω |
| [λΠ][λΠ] | λ with dependent types | |
| [λΠω][λΠω] | λΠ with type constructors | Calculus of Constructions | _Calculus of Constructions_ [[wiki](https://en.wikipedia.org/wiki/Calculus_of_constructions)]
| [λS][λS] | λΠω with self types | System S | _Self Types for Dependently Typed Lambda Encodings_ [[paper](https://fermat.github.io/document/papers/rta-tlca.pdf)]
| [λID][λID] | λΠω with inductive datatypes | Calculus of Inductive Constructions |
| [λCD][λCD] | λΠω with coinductive datatypes | Calculus of Coinductive Constructions  |
| [λPID][λPID] | predicative λΠω with inductive datatypes | Predicative Calculus of Coinductive Constructions |

## λ

**λ: Simply-typed λ-calculus.**

`Language/Lambda/` contains an intrinsically-typed implementation. Based on [_Programming Language Foundations in Agda –– DeBruijn: Intrinsically-typed de Bruijn representation_](https://plfa.github.io/DeBruijn/).

_Tasks._
- [x] Grammar
- [x] Typing
- [x] Reducing
- [ ] Examples
  - [x] simples
  - [ ] Church numerals


## λ2

**λ2: λ with type polymorphism (System F).**

`Lambda/Lambda2/` contain an intrinsically-typed implementation. Based on [_System F in Agda for Fun and Profit_](https://github.com/input-output-hk/plutus/tree/master/papers/system-f-in-agda).

_Tasks._
- [ ] Kinding
  - [ ] properties of `_≅ₛ_`
  - [ ] properties of `rename-⊨`
  - [ ] properties of `reflect`
  - [ ] properties of `reify`
  - [ ] interactions between `rename`, `substitute`, `extend`, `evaluate`, `reflect`, `reify`, and `_≅ₛ_`
  - [ ] properties of `_≅ₛ_`
  - [ ] properties of `_≅ₑ_`
  - [ ] completeness
  - [ ] stability
  - [ ] interactions between `rename`, `substitute`, weakenings, and single substitutions
- [x] Typing
- [ ] Normal Typing
  - [ ] normalization lemmas
  - [ ] `normalize-Type` cases:
    - [ ] ``` `fold```
    - [ ] ``` `unfold```
  - [ ] `progress` cases:
    - [ ] ```_`∙♯_```
    - [ ] ``` `unfold```
- [ ] Type Erasure
  - [ ] `erase-normalize-Type-≡`
  - [ ] erase-substitution lemmas

## λω

TODO

## λΠ

TODO

## λΠω

TODO

## λS

TODO

## λID

TODO

## λCID

TODO

## λPID

TODO


<!--  -->

[λ]: #λ
[λ2]: #λ2
[λω]: #λω
[λΠ]: #λΠ
[λΠω]: #λΠω
[λS]: #λS
[λID]: #λID
[λCD]: #λCD
[λPID]: #λPID
