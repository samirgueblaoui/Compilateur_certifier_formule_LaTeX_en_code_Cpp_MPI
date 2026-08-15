#pragma once
#include <string>
#include <memory>
#include <vector>
#include <iostream>


class ExprNode {
public:
    virtual ~ExprNode() = default;
    virtual void print(int indent = 0) const = 0;
};

using ExprPtr = std::shared_ptr<ExprNode>;

class IntNode : public ExprNode {
public:
    int value;
    IntNode(int value) : value(value) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "Int: " << value << std::endl;
    }
};

class DoubleNode : public ExprNode {
public:
    long double value;
    DoubleNode(double value) : value(value) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "Long Double: " << value << std::endl;
    }
};

class IdentNode : public ExprNode {
public:
    char value;
    IdentNode(char value) : value(value) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "Ident: " << value << std::endl;
    }
};


class BoolNode : public ExprNode {
public:
    bool value;
    BoolNode(bool value) : value(value) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "Bool: " << value << std::endl;
    }
};


class BinaryOpNode : public ExprNode {
public:
    std::string op;
    ExprPtr left;
    ExprPtr right;
    BinaryOpNode(std::string op, ExprPtr left, ExprPtr right)
        : op(op), left(left), right(right) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "BinaryOp: " << op << std::endl;
        left->print(indent + 2);
        right->print(indent + 2);
    }
};


class UnaryOpNode : public ExprNode {
public:
    std::string op;
    ExprPtr sub;
    UnaryOpNode(std::string op, ExprPtr sub)
        : op(op), sub(sub) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "UnaryOp: " << op << std::endl;
        sub->print(indent + 2);
    }
};



class FunCallNode : public ExprNode {
public:
    std::string name;
    std::vector<ExprPtr> sub;
    FunCallNode(std::string name, std::vector<ExprPtr> sub)
        : name(name), sub(sub) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "FunCallOp: " << name << std::endl;
        for (int i = 0; i < sub.size(); ++i)
            sub[i]->print(indent + 2);
    }
};


class BigSumNode : public ExprNode {
public:
    char indice;
    ExprPtr under;
    ExprPtr over;
    ExprPtr sub;
    ExprPtr condition; // Optional condition for the big sum
    BigSumNode(char indice, ExprPtr under, ExprPtr over, ExprPtr sub, ExprPtr condition = nullptr)
        : indice(indice), under(under), over(over), sub(sub), condition(condition) {}
    void print(int indent = 0) const override {
        std::cout << std::string(indent, ' ') << "BigSumOp: (indice = " << indice << " )" << std::endl;
            under->print(indent + 2);
            over->print(indent + 2);
            if (condition) {
                std::cout << std::string(indent, ' ') << "Cond, "; 
                condition->print(indent + 2);
            }
            sub->print(indent + 2);
    }
};





//#include <boost/preprocessor.hpp>

/* 


typedef enum { intNode, binaryOpNode, unaryOpNode } TypeNode;

#define X_DEFINE_ENUM_WITH_STRING_CONVERSIONS_TOSTRING_CASE(r, data, elem)    \
    case elem : return BOOST_PP_STRINGIZE(elem);

#define DEFINE_ENUM_WITH_STRING_CONVERSIONS(name, enumerators)                \
    enum name {                                                               \
        BOOST_PP_SEQ_ENUM(enumerators)                                        \
    };                                                                        \
                                                                              \
    inline const char* ToString(name v)                                       \
    {                                                                         \
        switch (v)                                                            \
        {                                                                     \
            BOOST_PP_SEQ_FOR_EACH(                                            \
                X_DEFINE_ENUM_WITH_STRING_CONVERSIONS_TOSTRING_CASE,          \
                name,                                                         \
                enumerators                                                   \
            )                                                                 \
            default: return "[Unknown " BOOST_PP_STRINGIZE(name) "]";         \
        }                                                                     \
    }

inline const char* TypeNodeToString(TypeNode v) {
    switch (v)
    {
        case intNode:      return "IntNode";
        case binaryOpNode: return "BinaryOpNode";
        case unaryOpNode:  return "UnaryOpNode";
        default:           return "[Unknown TypeNode or forget to implement in TypeNodeToString]";
    }
}
*/