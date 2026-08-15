#include "formexec_runner.hpp"

#include "formexec_cases.hpp"
#include "formexec_config.hpp"
#include "formexec_exec.hpp"
#include "formexec_output.hpp"
#include "formexec_pipeline.hpp"

#include <algorithm>
#include <map>
#include <regex>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>

// Exécute un cas du pont FormExec.
int executerPont(const ConfigExec& config) {
    try {
        std::filesystem::create_directories(config.dossierTrav);

        DonneesSection donnees = chargerSection(config.cheminConfig, config.section);
        std::vector<std::map<std::string, ValScalaire>> cas = construireCas(donnees);
        bool estMulti = !donnees.varsMulti.empty();

        std::vector<CasExec> resultats;
        resultats.reserve(cas.size());

        for (std::size_t indCas = 0; indCas < cas.size(); ++indCas) {
            std::filesystem::path cheminCpp =
                config.dossierTrav / ("formexec_case_" + std::to_string(indCas) + ".cpp");
            std::filesystem::path cheminExe =
                config.dossierTrav / ("formexec_case_" + std::to_string(indCas));

            genererProgramme(config.cheminFormule, cheminCpp, cas[indCas], donnees.optsSommes);

            std::string codeGenere = lireFichier(cheminCpp);
            ecrireFichier(
                cheminCpp,
                completerCodeGenere(codeGenere, cas[indCas], donnees.liaisonsFoncs)
            );
            compilerProgGenere(cheminCpp, cheminExe);

            CasExec casCour;
            for (int nbProc : donnees.procs) {
                casCour.mesures.push_back(executerProgGenere(cheminExe, nbProc));
            }
            resultats.push_back(casCour);
        }

        ecrireSortie(config.cheminSortie, resultats, donnees.procs, estMulti);
        return 0;
    } catch (const std::exception& erreur) {
        try {
            ecrireErreur(config.cheminSortie, erreur.what());
        } catch (...) {
        }
        return 1;
    }
}

// Exécute tous les cas d'un dossier FormExec.
int executerDossier(
    const std::filesystem::path& dossierSkel,
    const std::filesystem::path& cheminConfig,
    const std::filesystem::path& dossierTrav
) {
    try {
        if (!std::filesystem::exists(dossierSkel) || !std::filesystem::is_directory(dossierSkel)) {
            throw std::runtime_error("Dossier formSkel introuvable: " + dossierSkel.string());
        }

        std::regex motifFormule(R"(section([0-9]+)\.formula([0-9]+)\.formSkel\.in)");
        std::vector<std::tuple<int, int, std::filesystem::path>> formules;

        for (const auto& entree : std::filesystem::directory_iterator(dossierSkel)) {
            if (!entree.is_regular_file()) {
                continue;
            }

            std::smatch corresp;
            std::string nomFichier = entree.path().filename().string();
            if (!std::regex_match(nomFichier, corresp, motifFormule)) {
                continue;
            }

            int section = std::stoi(corresp[1].str());
            int formule = std::stoi(corresp[2].str());
            formules.push_back({section, formule, entree.path()});
        }

        // Trie les formules par section puis par numéro.
        std::sort(formules.begin(), formules.end(), [](const auto& gch, const auto& drt) {
            if (std::get<0>(gch) != std::get<0>(drt)) {
                return std::get<0>(gch) < std::get<0>(drt);
            }
            return std::get<1>(gch) < std::get<1>(drt);
        });

        if (formules.empty()) {
            throw std::runtime_error(
                "Aucun fichier sectionX.formulaY.formSkel.in trouve dans " + dossierSkel.string()
            );
        }

        int nbEchecs = 0;
        for (const auto& [section, formule, cheminEntree] : formules) {
            std::filesystem::path cheminSortie = cheminEntree;
            cheminSortie.replace_extension();
            cheminSortie += ".out";

            ConfigExec config;
            config.cheminFormule = cheminEntree;
            config.cheminSortie = cheminSortie;
            config.cheminConfig = cheminConfig;
            config.dossierTrav = dossierTrav /
                ("section" + std::to_string(section) + "_formula" + std::to_string(formule));
            config.section = section;

            if (executerPont(config) != 0) {
                ++nbEchecs;
            }
        }

        return nbEchecs == 0 ? 0 : 1;
    } catch (...) {
        return 1;
    }
}
