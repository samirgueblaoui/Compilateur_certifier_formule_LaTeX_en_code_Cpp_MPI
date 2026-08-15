#pragma once

#include <map>
#include <memory>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

// Types manipulés par le compilateur.
enum class Type {
    Ent,
    Flot,
    VectEnt,
    VectFlot
};

// Stratégies disponibles pour une somme.
enum class NatSomme {
    Seq,
    Par
};

// AST
struct Expr {
    // Détruit une expression.
    virtual ~Expr() = default;
};

using ExprPtr = std::shared_ptr<Expr>;

struct CstEnt : Expr {
    int val;

    // Crée une constante entière.
    explicit CstEnt(int v);
};

struct CstFlot : Expr {
    double val;

    // Crée une constante flottante.
    explicit CstFlot(double v);
};

struct Var : Expr {
    std::string nom;

    // Crée une variable.
    explicit Var(std::string n);
};

struct FoncUnaire : Expr {
    std::string nom;
    ExprPtr arg;

    // Crée un appel de fonction unaire.
    FoncUnaire(std::string f, ExprPtr e);
};

struct ExprBin : Expr {
    std::string op;
    ExprPtr gch;
    ExprPtr drt;

    // Crée une expression binaire.
    ExprBin(std::string opBin, ExprPtr g, ExprPtr d);
};

// Accès à un élément d'un vecteur avec un indice en base 0.
struct AccesVecteur : Expr {
    ExprPtr vecteur;
    ExprPtr indice;

    // Crée un accès à un vecteur.
    AccesVecteur(ExprPtr v, ExprPtr i);
};

struct Somme : Expr {
    NatSomme nat;
    std::string ind;
    ExprPtr bInf;
    ExprPtr bSup;
    ExprPtr corps;

    // Crée une somme.
    Somme(NatSomme n, std::string i, ExprPtr a, ExprPtr b, ExprPtr e);
};

// Environnement de typage des variables libres.
using Env = std::map<std::string, Type>;

// Environnement de typage des fonctions unaires.
using SigFoncUnaire = std::pair<Type, Type>;
using EnvFoncs = std::map<std::string, std::vector<SigFoncUnaire>>;

// Environnement de typage des fonctions binaires.
using SigFoncBin = std::tuple<Type, Type, Type>;
using EnvFoncsBin = std::map<std::string, std::vector<SigFoncBin>>;

// Détermine le type d'une expression.
Type typeDe(const ExprPtr& expr, Env env, const EnvFoncs& foncs, const EnvFoncsBin& foncsBin);

// Contexte d'exécution d'une somme parallèle.
struct CtxPar {
    std::string rang;
    std::string nbProc;
    std::string actif;
    int niveau = 0;
};

// Résultat de la compilation d'une expression.
struct ResCode {
    std::string code; // Code qui calcule l'expression.
    std::string res; // Nom de la variable contenant le résultat.
    Type type; // Type du résultat.
};

// Générateur de code pour les expressions.
class CompCode {
private:
    int cpt = 0;

    // Crée un nom de variable temporaire.
    std::string nouveauTemp();

public:
    // Compile une expression.
    ResCode comp(
        const ExprPtr& expr,
        Env env,
        const EnvFoncs& foncs,
        const EnvFoncsBin& foncsBin,
        const CtxPar& ctx
    );

    // Compile une somme.
    ResCode compSomme(
        const std::shared_ptr<Somme>& somme,
        Env env,
        const EnvFoncs& foncs,
        const EnvFoncsBin& foncsBin,
        const CtxPar& ctx
    );

    // Indente un bloc de code.
    static std::string indenter(const std::string& code);
};

// Génère le programme C++ complet.
std::string compilProg(const ExprPtr& expr, Env env, const EnvFoncs& foncs, const EnvFoncsBin& foncsBin);

// Écrit le programme généré.
void ecrireProg(const std::string& chemin, const std::string& programme);
