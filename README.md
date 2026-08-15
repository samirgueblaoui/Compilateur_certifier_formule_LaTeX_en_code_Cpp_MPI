# Compilateur de formules LaTeX vers C++/MPI

Ce compilateur transforme une expression mathématique écrite en LaTeX en un programme C++ exécutable avec MPI. Le projet réunit trois briques :

1. ExprLatex analyse la formule et construit un arbre syntaxique abstrait (AST) ;
2. le pont (`bridge`) convertit cet AST, lit la configuration FormExec et choisit la stratégie des sommes ;
3. le compilateur type l'expression puis génère le programme C++/MPI.

Deux modes d'utilisation sont disponibles :

- un mode simple, à partir d'un fichier `.tex` ;
- un mode FormExec intégré directement dans un document LaTeX.

## Sommaire

- [Prérequis](#prérequis)
- [Compilation](#compilation)
- [Mode simple](#mode-simple)
- [Mode FormExec](#mode-formexec)
- [Configuration JSON](#configuration-json)
- [Expressions prises en charge](#expressions-prises-en-charge)
- [Vecteurs](#vecteurs)

## Prérequis

Le projet nécessite :

- CMake 3.16 ou plus récent ;
- une installation MPI (`mpic++` et `mpirun`) ;
- la bibliothèque d'exécution C++ d'ANTLR4 ;
- `nlohmann-json` ;
- pour FormExec : Python 3, LaTeX et `pythontex`.

Sur macOS avec Homebrew :

```bash
brew install antlr4-cpp-runtime open-mpi cmake nlohmann-json
```

## Compilation

Depuis la racine du projet :

```bash
cmake -S . -B build
cmake --build build -j4
```

### Options utiles

```bash
cmake -S . -B build \
  -DLATEX_INPUT_FILE=/chemin/formule.tex \
  -DGENERATED_CPP_FILE=/chemin/programme.cpp \
  -DRUN_MPI_PROCESSES=4
```

Valeurs par défaut :

- entrée : `exprlatex/input.tex` ;
- C++ généré : `compilateur/src/compile.cpp` ;
- exécution de `run_generated` : 4 processus.

## Mode simple

### 1. Écrire une formule

Dans `exprlatex/input.tex`, par exemple :

```tex
\sum_{i=1}^{10} i
```

### 2. Générer et compiler

```bash
cmake --build build --target generated_mpi_program
```

### 3. Exécuter

```bash
mpirun -np 4 ./build/generated_mpi_program
```

Ou avec CMake :

```bash
cmake --build build --target run_generated
```

### Variables et fonctions libres

Le mode simple ne lit pas `FormExec/config.json`.

- une variable libre est initialisée à zéro dans le C++ généré et marquée par
  `// variable libre a modifier` ;
- une fonction non native produit un corps marqué
  `// corps a modifier` qui doit être remplacé par une implémentation C++.

## Mode FormExec

FormExec extrait les formules d'un document LaTeX, génère des fichiers d'entrée, appelle le compilateur puis relit les résultats.

Depuis la racine :

```bash
cd FormExec
pdflatex -shell-escape article.tex
cd ..

cmake --build build --target formexec_bridge_driver
./build/formexec_bridge_driver FormExec/formSkel FormExec/config.json

cd FormExec
pdflatex -shell-escape article.tex
pdflatex -shell-escape article.tex
```

### Traiter une seule formule

```bash
./build/formexec_bridge_driver \
  FormExec/formSkel/section3.formula1.formSkel.in \
  3 \
  FormExec/formSkel/section3.formula1.formSkel.out \
  FormExec/config.json \
  build/formexec_runs/section3_formula1
```

Syntaxe générale :

```text
./build/formexec_bridge_driver \
  <formula_in> <section> <output_out> <config_json> [work_dir]
```

## Configuration JSON

### Exemple minimal

```json
{
  "sumStrategy": {
    "assumedProcesses": 4,
    "minParallelIterations": 8
  },
  "functions": [
    {
      "latex": "\\sin",
      "c++": "std::sin",
      "type": {
        "input": ["R"],
        "output": "R",
        "cost": { "c++": 12.0 }
      }
    }
  ],
  "environments": [
    {
      "section": 1,
      "x": 0.5,
      "n": 100,
      "processors": [1, 2, 4]
    }
  ]
}
```

### Variables fixes

```json
{
  "x": 2.5,
  "n": 100
}
```

### Variables MULTI

```json
{
  "n": [10, 20, 30, 40],
  "x": [0.25, 0.75, 1.25, 1.75]
}
```

Le premier cas utilise `n=10` et `x=0.25`, le deuxième `n=20` et `x=0.75`, etc. Toutes les listes MULTI d'une section doivent avoir la même longueur.

### Nombre de processus

```json
"processors": [1, 2, 4]
```

Le programme est exécuté successivement avec chacun de ces nombres de processus.

### Fonctions

Une fonction LaTeX peut être reliée à une fonction C++ :

```json
{
  "latex": "\\cos",
  "c++": "std::cos",
  "type": {
    "input": ["R"],
    "output": "R",
    "cost": { "c++": 13.0 }
  }
}
```

Les fonctions binaires personnalisées utilisent deux types d'entrée. Elles peuvent être écrites sous la forme `\hypot(x,y)` ou `\hypot{x}{y}` :

```json
{
  "latex": "\\hypot",
  "c++": "std::hypot",
  "type": {
    "input": ["R", "R"],
    "output": "R",
    "cost": { "c++": 8.0 }
  }
}
```

Le coût numérique est facultatif. Lorsqu'il est présent, il alimente également le modèle de choix des sommes.

Les opérations `+`, `-`, `*` et `/` n'ont pas besoin d'être définies. La division est toujours flottante : `\frac{7}{2}` = `3.5`.

## Expressions prises en charge

La partie reliée au générateur C++ couvre :

- constantes entières et flottantes ;
- variables constituées actuellement d'une lettre latine ;
- parenthèses ;
- addition, soustraction et multiplication ;
- multiplication implicite, par exemple `2x` ;
- division directe ou avec `\frac` ;
- fonctions unaires configurées, par exemple `\sin`, `\cos` ou `\sqrt` ;
- fonctions binaires configurées, par exemple `\hypot(x,y)` ;
- sommes simples et imbriquées sans condition ;
- accès vectoriels `v[i]` et `v_i` ;
- norme euclidienne et norme de Frobenius des vecteurs.

Exemples :

```tex
3 + 2 \times 5
\frac{x+1}{n}
\sin(x) + \cos(2x)
\hypot(3,4)
\sum_{i=1}^{n} i
\sum_{i=0}^{n}\left(v_i + \sin(i)\right)
\sum_{i=0}^{n}\sum_{j=0}^{n}(i+j)
```

## Vecteurs

### Syntaxe des accès

Les formes suivantes sont équivalentes :

```tex
v[i]
v_i
```

Les indices sont en base 0. Pour parcourir un vecteur de quatre éléments :

```tex
\sum_{i=0}^{3} v_i
```

### Vecteur dans le JSON

Une liste numérique directe étant réservée à `MULTI`, un vecteur utilise un objet `values` :

```json
"v": {
  "values": [1.0, 2.0, 3.0, 4.0]
}
```

Le type est déduit automatiquement :

- uniquement des entiers : `Type::VectEnt`, représenté par `std::vector<int>` ;
- au moins un flottant non entier : `Type::VectFlot`, représenté par `std::vector<double>`.

### Plusieurs vecteurs en mode MULTI

```json
{
  "v": [
    { "values": [1, 2, 3] },
    { "values": [4, 5, 6] }
  ],
  "n": [2, 2]
}
```

Le premier cas utilise `(1,2,3)` et le second `(4,5,6)`.

### Vecteur provenant d'un fichier

```json
"v": {
  "file": "data/v.data",
  "reading": "partial"
}
```

Les chemins relatifs sont résolus depuis le dossier contenant `config.json`.

Formats acceptés :

- texte simple avec nombres séparés par espaces, lignes ou virgules ;
- MatrixMarket vector array real general ;
- MatrixMarket vector coordinate real general ;

Exemple texte :

```text
# commentaire
1.0, 2.5
3.0 4.25
```

Exemple MatrixMarket dense :

```text
%%MatrixMarket vector array real general
4
1.0
2.5
3.0
4.25
```

Exemple MatrixMarket creux :

```text
%%MatrixMarket vector coordinate real general
5 3
1 2.5
3 -1.0
5 4.0
```

Les indices MatrixMarket sont en base 1.

### Normes

```tex
\lVert v \rVert
\lVert v \rVert_F
```

Pour un vecteur, les deux formes calculent actuellement :

```text
sqrt(v[0]^2 + v[1]^2 + ...)
```
