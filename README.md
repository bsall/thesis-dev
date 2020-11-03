# Programmation impérative par raffinements avec l'assistant de preuve Coq

Ce développement nécessite Coq 8.9.1. Le projet peut être compilé en tapant la commande : *make -f CoqMakefile*. L'installation de [Proof General](https://proofgeneral.github.io/) et [company coq](https://github.com/cpitclaudel/company-coq) est recommandée. Le développement comporte deux parties, une partie [théorique](./src/theory) et quelques [exemples](./src/examples).

## Théorie

Dans [Statement.v](./src/theory/Statement.v) on trouve la syntaxe d'un langage impératif classique. Le fichier [HoareWp.v](./src/theory/HoareWp.v) contient une logique de Hoare et une définition du raffinement de programmes à partir de cette logique. On définit aussi une sémantique prédicative du langage dans [Predicative.v](./src/theory/Predicative.v), et l'équivalence (modulo raffinement) entre cette 
sémantique et la logique de Hoare est établie dans [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v). Pour faciliter les raisonnements, on s'appuie sur un calcul de la plus faible pré-spécification défini dans [Wpr.v](src/theory/Wpr.v). Enfin, on trouvera [CbC.v](./src/theory/CbC.v) une formalisation d'un ensemble de règles de développement permettant d'obtenir des résultats corrects par construction. La correction et la complétude de ces règles est également établie dans ce même fichier.

## Exemples

Le dossier [examples](./src/examples) contient des illustrations de preuve de programmes avec la sémantique prédicative directement, avec le calcul de la plus faible pré-spécification, et avec les règles de la correction par construction. En particulier, on trouvera dans [Sqrt.v](./src/examples/Design_Sqrt.v) le développement par raffinements d'un algorithme de calcul de la racine carrée d'un entier.

## Description
La théorie formalisée par ce développement Coq est décrite dans ce [manuscrit](./sall-manuscrit.pdf). Le tableau ci-dessous fait correspondre les définitions et résultats principaux avec leur nom dans les fichiers .v.

| Définitions | Nom | Fichier |
| ----------- | --- | ------- |
| [Définition 8](./src/theory/LeastFixpoint.v#L7) | lfp | [LeastFixpoint.v](./src/theory/LeastFixpoint.v) |
| [Lemme 1](./src/theory/LeastFixpoint.v#L28) | f_lfp | [LeastFixpoint.v](./src/theory/LeastFixpoint.v) |
| [Lemme 2](./src/theory/LeastFixpoint.v#L51) | lfp_fix | [LeastFixpoint.v](./src/theory/LeastFixpoint.v) |
| Définition 9 | tcl | [TransitiveClosure.v](./src/theory/TransitiveClosure.v) |
| Lemme 3 | tcl_trans | [TransitiveClosure.v](./src/theory/TransitiveClosure.v) |
| Lemme 4 | tcl_fix | [TransitiveClosure.v](./src/theory/TransitiveClosure.v) |
| Syntaxe (Figure 4.1) | Statement | [Statement.v](./src/theory/Statement.v) |
| Sémantique prédicative (Figure 4.2) | pred | [Predicative.v](./src/theory/Predicative.v) |
| Définition 13 (Composition démoniaque) | fn | [DemonicComposition.v](./src/theory/DemonicComposition.v) |
| Définition 13 (Composition angélique) | fn | [AngelicComposition.v](./src/theory/AngelicComposition.v) |
| Lemme 5 | right_monotonic | [DemonicComposition.v](./src/theory/DemonicComposition.v) |
| Lemme 6 (1) | while_fix | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 6 (2) | while_ind | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 7 | ex_while_ind | [Predicative.v](./src/theory/Predicative.v) |
| Théorème 1 | while_well_founded | [Predicative.v](./src/theory/Predicative.v) |
| Définition 14 | refines | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 8 (1) | refines_reflexive | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 8 (3) | refines_trans | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 9 (1) | If_monotonic_refines | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 9 (2) | Seq_monotonic_refines | [Predicative.v](./src/theory/Predicative.v) |
| Lemme 9 (3) | While_monotonic_refines | [Predicative.v](./src/theory/Predicative.v) |
| Définition 15 et Figure 4.3 | ValidHoareTriple | [ValidHoareTriple.v](./src/theory/HoareWp.v) |
| Lemme 10 | hoare_pred | [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v) |
| Définition 16 et Figure 4.3 | refines | [ValidHoareTriple.v](./src/theory/HoareWp.v) |
| Lemme 11 | triple_ext_triple | [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v) |
| Théorème 2 | extended_definition_iff_simple_definition | [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v) |
| Théorème 3 | hoare_refines_iff_pred_refines | [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v) |
| Sémantique prédicative (Figure 5.1) | pred | [ImprovedPredicative.v](./src/theory/ImprovedPredicative.v) |
| Lemme 12 | pred_opt_pred_seq | [ImprovedPredicative.v](./src/theory/ImprovedPredicative.v) |
| Theorem 4 | pred_old_pred | [ImprovedPredicative.v](./src/theory/ImprovedPredicative.v) |
| Définition 19 | wpr_spec | [Wpr.v](./src/theory/Wpr.v) |
| Définition 20 | wpr | [Wpr.v](./src/theory/Wpr.v) |
| Lemme 14 (1) | wpr_while_construct, wpr_while_destruct | [Wpr.v](./src/theory/Wpr.v) |
| Lemme 14 (2) | wpr_while_ind | [Wpr.v](./src/theory/Wpr.v) |
| Lemme 15 | wpr_pred | [Wpr.v](./src/theory/Wpr.v) |
| Théorème 4 | wpr_refines | [Wpr.v](./src/theory/Wpr.v) |
| Lemme 16 | wfd_while_iff_if | [Predicative.v](./src/theory/Predicative.v) |
| Théorème 6 | while_rule_sound_and_complete | [Predicative.v](./src/theory/Predicative.v) |
| Langage de développement (Figure 6.2) | Dev | [CbC.v](./src/theory/CbC.v) |
| Définition 21 | dsem | [CbC.v](./src/theory/CbC.v) |
| Définition 23 | CbC | [CbC.v](./src/theory/CbC.v) |
| Théorème 7 | wpr_wpr' | [CbC.v](./src/theory/CbC.v) |
| Théorème 8 | soundness | [CbC.v](./src/theory/CbC.v) |
| Théorème 9 | completeness | [CbC.v](./src/theory/CbC.v) |
