#include "formexec_exec.hpp"

#include <array>
#include <chrono>
#include <cstdio>
#include <stdexcept>
#include <string>

namespace {

// Protège un chemin destiné à une commande shell.
std::string protegerChemin(const std::filesystem::path& chemin) {
    std::string texte = chemin.string();
    std::string sortie = "'";
    for (char c : texte) {
        if (c == '\'') {
            sortie += "'\\''";
        } else {
            sortie += c;
        }
    }
    sortie += "'";
    return sortie;
}

// Exécute une commande et récupère sa sortie texte.
std::string executerCommande(const std::string& commande, int& codeSortie) {
    FILE* flux = popen(commande.c_str(), "r");
    if (flux == nullptr) {
        throw std::runtime_error("Impossible de lancer la commande: " + commande);
    }

    std::string sortie;
    std::array<char, 4096> tampon{};
    while (fgets(tampon.data(), static_cast<int>(tampon.size()), flux) != nullptr) {
        sortie += tampon.data();
    }

    codeSortie = pclose(flux);
    return sortie;
}

} // namespace

// Compile le C++ généré en exécutable MPI.
void compilerProgGenere(
    const std::filesystem::path& cheminCpp,
    const std::filesystem::path& cheminExe
) {
    std::string commande =
        "mpic++ " + protegerChemin(cheminCpp) + " -o " + protegerChemin(cheminExe);
    int codeSortie = 0;
    std::string sortie = executerCommande(commande + " 2>&1", codeSortie);
    if (codeSortie != 0) {
        throw std::runtime_error("Echec compilation MPI:\n" + sortie);
    }
}

// Exécute le programme MPI et mesure sa durée.
MesureExec executerProgGenere(const std::filesystem::path& cheminExe, int nbProc) {
    std::string commande =
        "mpirun -np " + std::to_string(nbProc) + " " + protegerChemin(cheminExe) + " 2>&1";

    auto debut = std::chrono::steady_clock::now();
    int codeSortie = 0;
    std::string sortie = executerCommande(commande, codeSortie);
    auto fin = std::chrono::steady_clock::now();

    if (codeSortie != 0) {
        throw std::runtime_error("Echec execution MPI:\n" + sortie);
    }

    while (!sortie.empty() && (sortie.back() == '\n' || sortie.back() == '\r')) {
        sortie.pop_back();
    }

    MesureExec mesure;
    mesure.val = sortie;
    mesure.dureeNs = std::chrono::duration_cast<std::chrono::nanoseconds>(fin - debut).count();
    return mesure;
}
