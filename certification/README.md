# Certification Coq


## Ordre des fichiers

1. `C00_Source.v` : langage source, typage et sémantique grand pas.
2. `C01_TargetCompiler.v` : langage cible, contextes et compilateur.
3. `C02_SmallStep.v` : sémantique petit pas locale et globale.
4. `C03_Invariants.v` : relations de simulation, fraîcheur et préservation.
5. `C04_SequentialSum.v` : compilation et correction de `SumSeq`.
6. `C05_LocalCorrectness.v` : correction sémantique locale.
7. `C06_GlobalExecution.v` : assemblage des exécutions locales.
8. `C07_SumParSimple.v` : lemmes propres à une somme parallèle simple.
9. `C08_Correctness.v` : théorèmes de correction établis.
10. `All.v` : point d'entrée qui réexporte toute la formalisation.

## Portée

Le dossier s'arrête à la correction d'un `SumPar` simple. Les définitions générales du langage et du compilateur restent fidèles au document LaTeX, mais les invariants et preuves consacrés aux `SumPar` imbriqués ne sont pas inclus.

