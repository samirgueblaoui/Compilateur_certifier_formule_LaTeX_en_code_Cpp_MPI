#include "formexec_output.hpp"

#include <fstream>
#include <sstream>
#include <stdexcept>

namespace {

// Formate la liste des nombres de processus.
std::string joindreProcs(const std::vector<int>& procs, const std::string& sep) {
    std::ostringstream flux;
    for (std::size_t i = 0; i < procs.size(); ++i) {
        if (i != 0) {
            flux << sep;
        }
        flux << procs[i];
    }
    return flux.str();
}

} // namespace

// Écrit un fichier .formSkel.out au format FormExec.
void ecrireSortie(
    const std::filesystem::path& cheminSortie,
    const std::vector<CasExec>& cas,
    const std::vector<int>& procs,
    bool estMulti
) {
    std::ofstream sortie(cheminSortie);
    if (!sortie.is_open()) {
        throw std::runtime_error(
            "Impossible d'ecrire le fichier de sortie FormExec: " + cheminSortie.string()
        );
    }

    if (!estMulti) {
        sortie << "SOLO\n";
        sortie << joindreProcs(procs, ",") << "\n";
        for (const MesureExec& mesure : cas.front().mesures) {
            sortie << mesure.val << "\n";
            sortie << mesure.dureeNs << "\n";
        }
        return;
    }

    sortie << "MULTI\n";
    sortie << joindreProcs(procs, " ") << "\n";
    for (std::size_t indProc = 0; indProc < procs.size(); ++indProc) {
        for (const CasExec& casCour : cas) {
            sortie << casCour.mesures[indProc].val << "\n";
            sortie << casCour.mesures[indProc].dureeNs << "\n";
        }
    }
}

// Écrit un fichier d'erreur lisible par FormExec.
void ecrireErreur(const std::filesystem::path& cheminSortie, const std::string& message) {
    std::ofstream sortie(cheminSortie);
    if (!sortie.is_open()) {
        throw std::runtime_error(
            "Impossible d'ecrire le fichier erreur FormExec: " + cheminSortie.string()
        );
    }
    sortie << "ERROR\n";
    sortie << message << "\n";
}
