#include "antlr4-runtime.h"
#include <vector>

using namespace antlr4;

class VectorTokenSource : public antlr4::TokenSource {
private:    
    std::vector<std::unique_ptr<antlr4::Token>> tokens;
    size_t i = 0;

public:
    VectorTokenSource(std::vector<std::unique_ptr<antlr4::Token>> t) : tokens(std::move(t)) {}

    std::unique_ptr<antlr4::Token> nextToken() override {
        if (i >= tokens.size())
            return std::unique_ptr<antlr4::Token>(new antlr4::CommonToken(antlr4::Token::EOF));
      
        return std::move(tokens[i++]);
    }

    // --- REQUIRED BY INTERFACE ---

    antlr4::CharStream* getInputStream() override { return nullptr; }
    
    size_t getLine() const { return 0; }
    
    antlr4::TokenFactory<antlr4::CommonToken>* getTokenFactory() override { return nullptr; }

    size_t getCharPositionInLine() { return 0;  }


    void setInputStream(CharStream* input) { 
        // do nothing
    }        

    std::string getSourceName() { return "<VectorTokenSource>";  }

    void setTokenFactory(TokenFactory<CommonToken>* factory) {
        // do nothing    
    }
};