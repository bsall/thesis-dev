# Programmation impérative par raffinements avec l'assistant de preuve Coq

Ce développement nécessite Coq 8.9.1. Le projet peut être compilé en tapant la commande : *make -f CoqMakefile*.
L'installation de [Proof General](https://proofgeneral.github.io/) et [company coq](https://github.com/cpitclaudel/company-coq) est recommandée.
Le développement comporte deux parties, une partie [théorique](./src/theory) et quelques [exemples](./src/examples).

## Théorie

Dans [Statement.v](./src/theory/Statement.v) on trouve la syntaxe d'un langage impératif classique.
Le fichier [FloydHoareWp.v](./src/theory/FloydHoareWp.v) contient une logique de Hoare et une définition 
du raffinement de programmes à partir de cette logique. On définit aussi une sémantique prédicative du 
langage dans [Predicative.v](./src/theory/Predicative.v), et l'équivalence (modulo raffinement) entre cette 
sémantique et la logique de Hoare est établie dans [HoareWp_Predicative.v](./src/theory/HoareWp_Predicative.v).
Pour faciliter les raisonnements, on s'appuie sur un calcul de la plus faible pré-spécification défini dans [Wpr.v](src/theory/Wpr.v).
Enfin, on trouvera [CbC.v](./src/theory/CbC.v) une formalisation d'un ensemble de règles de développement 
permettant d'obtenir des résultats corrects par construction. La correction et la complétude de ces règles 
est également établie dans ce même fichier.

## Exemples

Le dossier [examples](./src/examples) contient des illustrations de preuve de programmes avec la sémantique 
prédicative directement, avec le calcul de la plus faible pré-spécification, et avec les règles de la correction 
par construction. En particulier, on trouvera dans [Sqrt.v](./src/examples/Design_Sqrt.v) le développement par 
raffinements d'un algorithme de calcul de la racine carrée d'un entier.
