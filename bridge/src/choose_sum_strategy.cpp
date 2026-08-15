#include "choose_sum_strategy.hpp"

#include <algorithm>
#include <cmath>
#include <set>

namespace {

// Retourne le coût d'une fonction unaire.
double coutFoncUnaire(const std::string& nom, const OptsStrSom& opts) {
    auto itCout = opts.coutsFoncsUnaires.find(nom);
    if (itCout != opts.coutsFoncsUnaires.end()) {
        return itCout->second;
    }
    return opts.coutFoncUnaireDef;
}

// Retourne le coût d'une fonction binaire.
double coutFoncBinaire(const std::string& nom, const OptsStrSom& opts) {
    if (nom == "+" || nom == "-" || nom == "*") {
        return opts.coutOpArith;
    }

    auto itCout = opts.coutsFoncsBin.find(nom);
    if (itCout != opts.coutsFoncsBin.end()) {
        return itCout->second;
    }
    return opts.coutFoncBinDef;
}

// Détecte une somme parallèle dans une expression.
bool aSommeParDansCorps(const ExprPtr& expr) {
    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        if (somme->nat == NatSomme::Par) {
            return true;
        }
        return aSommeParDansCorps(somme->bInf)
            || aSommeParDansCorps(somme->bSup)
            || aSommeParDansCorps(somme->corps);
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        return aSommeParDansCorps(fonc->arg);
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        return aSommeParDansCorps(exprBin->gch)
            || aSommeParDansCorps(exprBin->drt);
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        return aSommeParDansCorps(acces->vecteur)
            || aSommeParDansCorps(acces->indice);
    }

    return false;
}

// Calcule statiquement la taille de l'intervalle d'une somme.
std::optional<int> tailleIntervStat(const std::shared_ptr<Somme>& somme) {
    auto bInf = evalEntStat(somme->bInf);
    auto bSup = evalEntStat(somme->bSup);
    if (!bInf.has_value() || !bSup.has_value()) {
        return std::nullopt;
    }

    return *bSup - *bInf + 1;
}

// Retourne la taille connue d'un intervalle ou sa valeur par défaut.
double tailleIntervOuDefaut(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    auto nbIter = tailleIntervStat(somme);
    if (nbIter.has_value()) {
        return static_cast<double>(std::max(*nbIter, 0));
    }
    return static_cast<double>(opts.tailleIntervDef);
}

// Spécialise récursivement une expression avec les valeurs connues.
ExprPtr specialiserRec(
    const ExprPtr& expr,
    const EnvValsConnues& vals,
    const OptsStrSom& opts,
    std::set<std::string> indicesLies
) {
    if (auto cstEnt = std::dynamic_pointer_cast<CstEnt>(expr)) {
        return std::make_shared<CstEnt>(cstEnt->val);
    }

    if (auto cstFlot = std::dynamic_pointer_cast<CstFlot>(expr)) {
        return std::make_shared<CstFlot>(cstFlot->val);
    }

    if (auto var = std::dynamic_pointer_cast<Var>(expr)) {
        if (indicesLies.contains(var->nom)) {
            return std::make_shared<Var>(var->nom);
        }

        auto itVal = vals.find(var->nom);
        if (itVal == vals.end()) {
            return std::make_shared<Var>(var->nom);
        }

        if (itVal->second.type == Type::Ent) {
            return std::make_shared<CstEnt>(itVal->second.valEnt);
        }
        return std::make_shared<CstFlot>(itVal->second.valFlot);
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        return std::make_shared<FoncUnaire>(
            fonc->nom,
            specialiserRec(fonc->arg, vals, opts, std::move(indicesLies))
        );
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        return std::make_shared<ExprBin>(
            exprBin->op,
            specialiserRec(exprBin->gch, vals, opts, indicesLies),
            specialiserRec(exprBin->drt, vals, opts, std::move(indicesLies))
        );
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        return std::make_shared<AccesVecteur>(
            specialiserRec(acces->vecteur, vals, opts, indicesLies),
            specialiserRec(acces->indice, vals, opts, std::move(indicesLies))
        );
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        auto indicesSomme = indicesLies;
        indicesSomme.insert(somme->ind);

        auto specialisee = std::make_shared<Somme>(
            NatSomme::Seq,
            somme->ind,
            specialiserRec(somme->bInf, vals, opts, indicesLies),
            specialiserRec(somme->bSup, vals, opts, indicesLies),
            specialiserRec(somme->corps, vals, opts, std::move(indicesSomme))
        );
        specialisee->nat = choisitStrSom(specialisee, opts);
        return specialisee;
    }

    return expr;
}

}

// Évalue statiquement les expressions entières élémentaires.
std::optional<int> evalEntStat(const ExprPtr& expr) {
    if (auto cst = std::dynamic_pointer_cast<CstEnt>(expr)) {
        return cst->val;
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        auto gch = evalEntStat(exprBin->gch);
        auto drt = evalEntStat(exprBin->drt);
        if (!gch.has_value() || !drt.has_value()) {
            return std::nullopt;
        }

        if (exprBin->op == "+") {
            return *gch + *drt;
        }
        if (exprBin->op == "-") {
            return *gch - *drt;
        }
        if (exprBin->op == "*") {
            return *gch * *drt;
        }
    }

    return std::nullopt;
}

// Estime le travail nécessaire pour une expression.
double estimeTravExpr(const ExprPtr& expr, const OptsStrSom& opts) {
    if (std::dynamic_pointer_cast<CstEnt>(expr) ||
        std::dynamic_pointer_cast<CstFlot>(expr) ||
        std::dynamic_pointer_cast<Var>(expr)) {
        return 1.0;
    }

    if (auto fonc = std::dynamic_pointer_cast<FoncUnaire>(expr)) {
        return coutFoncUnaire(fonc->nom, opts) + estimeTravExpr(fonc->arg, opts);
    }

    if (auto exprBin = std::dynamic_pointer_cast<ExprBin>(expr)) {
        double coutOp = coutFoncBinaire(exprBin->op, opts);
        return coutOp
            + estimeTravExpr(exprBin->gch, opts)
            + estimeTravExpr(exprBin->drt, opts);
    }

    if (auto acces = std::dynamic_pointer_cast<AccesVecteur>(expr)) {
        return 1.0
            + estimeTravExpr(acces->vecteur, opts)
            + estimeTravExpr(acces->indice, opts);
    }

    if (auto somme = std::dynamic_pointer_cast<Somme>(expr)) {
        if (somme->nat == NatSomme::Par) {
            return estimeCoutSomPar(somme, opts);
        }
        return estimeCoutSomSeq(somme, opts);
    }

    return opts.coutFoncBinDef;
}

// Estime le coût séquentiel d'une somme.
double estimeCoutSomSeq(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    double nbIter = tailleIntervOuDefaut(somme, opts);
    return estimeTravExpr(somme->bInf, opts)
        + estimeTravExpr(somme->bSup, opts)
        + nbIter * (estimeTravExpr(somme->corps, opts) + opts.coutAcc);
}

// Estime le coût parallèle simple d'une somme.
double estimeCoutSomParSimple(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    double nbIter = tailleIntervOuDefaut(somme, opts);
    double nbProc = static_cast<double>(std::max(opts.nbProc, 1));
    double iterLoc = std::ceil(nbIter / nbProc);
    double trav =
        estimeTravExpr(somme->bInf, opts)
        + estimeTravExpr(somme->bSup, opts)
        + iterLoc * (estimeTravExpr(somme->corps, opts) + opts.coutAcc);
    double volCom = opts.volReduc;
    double nbSynchro = 1.0;

    return trav + volCom * opts.coutCom + nbSynchro * opts.coutSynchro;
}

// Estime le coût parallèle imbriqué d'une somme.
double estimeCoutSomParImb(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    double nbIter = tailleIntervOuDefaut(somme, opts);
    int nbProc = std::max(opts.nbProc, 1);
    int nbGrp = nbProc > 1 ? std::min(std::max(opts.nbGrpImb, 1), nbProc) : 1;
    double nbGrpReel = static_cast<double>(nbGrp);
    double iterExtParGrp = std::ceil(nbIter / nbGrpReel);
    double trav =
        estimeTravExpr(somme->bInf, opts)
        + estimeTravExpr(somme->bSup, opts)
        + iterExtParGrp * (estimeTravExpr(somme->corps, opts) + opts.coutAcc);

    double volCom = opts.volReduc;
    double nbSynchro = 1.0;
    double surcoutGrp = nbIter;

    return trav + surcoutGrp + volCom * opts.coutCom + nbSynchro * opts.coutSynchro;
}

// Estime le meilleur coût parallèle d'une somme.
double estimeCoutSomPar(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    if (aSommeParDansCorps(somme->corps)) {
        return estimeCoutSomParImb(somme, opts);
    }
    return estimeCoutSomParSimple(somme, opts);
}

// Choisit la stratégie la moins coûteuse pour une somme.
NatSomme choisitStrSom(const std::shared_ptr<Somme>& somme, const OptsStrSom& opts) {
    auto nbIter = tailleIntervStat(somme);
    if (nbIter.has_value() && *nbIter < opts.minIterPar) {
        return NatSomme::Seq;
    }

    auto somSeq = std::make_shared<Somme>(
        NatSomme::Seq,
        somme->ind,
        somme->bInf,
        somme->bSup,
        somme->corps
    );

    auto somPar = std::make_shared<Somme>(
        NatSomme::Par,
        somme->ind,
        somme->bInf,
        somme->bSup,
        somme->corps
    );

    double coutSeq = estimeCoutSomSeq(somSeq, opts);
    double coutPar = estimeCoutSomPar(somPar, opts);

    return coutPar < coutSeq ? NatSomme::Par : NatSomme::Seq;
}

// Spécialise une expression et recalcule la stratégie de ses sommes.
ExprPtr specialiserSommes(
    const ExprPtr& expr,
    const EnvValsConnues& vals,
    const OptsStrSom& opts
) {
    return specialiserRec(expr, vals, opts, {});
}
