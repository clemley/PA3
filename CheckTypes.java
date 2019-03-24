package ast_visitors;

/** 
 * CheckTypes
 * 
 * This AST visitor traverses a MiniJava Abstract Syntax Tree and checks
 * for a number of type errors.  If a type error is found a SymanticException
 * is thrown
 * 
 * CHANGES to make next year (2012)
 *  - make the error messages between *, +, and - consistent <= ??
 *
 * Bring down the symtab code so that it only does get and set Type
 *  for expressions
 */

import ast.node.*;
import ast.visitor.DepthFirstVisitor;
import java.util.*;

import symtable.SymTable;
import symtable.Type;
import exceptions.InternalException;
import exceptions.SemanticException;

public class CheckTypes extends DepthFirstVisitor
{
    
   private SymTable mCurrentST;
   
   public CheckTypes(SymTable st) {
     if(st==null) {
          throw new InternalException("unexpected null argument");
      }
      mCurrentST = st;
   }
   
   //========================= Overriding the visitor interface

   public void defaultOut(Node node) {
       System.err.println("Node not implemented in CheckTypes, " + node.getClass());
   }
   
   public void outAndExp(AndExp node)
   {
     if(this.mCurrentST.getExpType(node.getLExp()) != Type.BOOL) {
       throw new SemanticException(
         "Invalid left operand type for operator &&",
         node.getLExp().getLine(), node.getLExp().getPos());
     }

     if(this.mCurrentST.getExpType(node.getRExp()) != Type.BOOL) {
       throw new SemanticException(
         "Invalid right operand type for operator &&",
         node.getRExp().getLine(), node.getRExp().getPos());
     }

     this.mCurrentST.setExpType(node, Type.BOOL);
   }
  
   public void outPlusExp(PlusExp node)
   {
       Type lexpType = this.mCurrentST.getExpType(node.getLExp());
       Type rexpType = this.mCurrentST.getExpType(node.getRExp());
       if ((lexpType==Type.INT  || lexpType==Type.BYTE) &&
           (rexpType==Type.INT  || rexpType==Type.BYTE)
          ){
           this.mCurrentST.setExpType(node, Type.INT);
       } else {
           throw new SemanticException(
                   "Operands to + operator must be INT or BYTE",
                   node.getLExp().getLine(),
                   node.getLExp().getPos());
       }

   }

   private static class TypeCheckVisitor extends ast_visitors {
    private TypeSymTab SymTable = new TypeSymTab();
    private Type lastType = VoidType.instance;

    public TypeCheckVisitor(Map<String, Type> initialTypes) {
        SymTable.putAll(initialTypes);
    }

    @Override
    public void DotVisitor(Declaration decl) {
        if (SymTable.containsKey(decl.varName)) {
            throw new TypeError("Variable " + decl.varName + " already declared.");
        }
        SymTable.put(decl.varName, decl.type);
        
        decl.expr.accept(this);
        if (!canBeAssigned(lastType, decl.type)) {
            throw new TypeError("Variable '" + decl.varName + "' cannot be initialized with a " + lastType);
        }
        
        lastType = VoidType.instance;
    }

    @Override
    public void DotVisitor(Assignment assignment) {
        Type varTy = SymTable.get(assignment.varName);
        if (varTy == null) {
            throw new TypeError("Assignment to undeclared variable: " + assignment.varName);
        }
        
        assignment.expr.accept(this);
        if (!canBeAssigned(lastType, varTy)) {
            throw new TypeError("Cannot assign " + lastType + " to '" + assignment.varName + "' (of type " + varTy + ")");
        }
        
        lastType = VoidType.instance;
    }

    @Override
    public void DotVisitor(Block block) {
        SymTable.pushState();
        for (Statement stmt : block.statements) {
            stmt.accept(this);
        }
        SymTable.popState();
        
        lastType = VoidType.instance;
    }

    @Override
    public void DotVisitor(IfStatement ifStmt) {
        ifStmt.condition.accept(this);
        if (!lastType.equals(BoolType.instance)) {
            throw new TypeError("If condition was " + lastType + " instead of bool");
        }
        
        SymTable.pushState();
        ifStmt.thenClause.accept(this);
        SymTable.popState();
        SymTable.pushState();
        ifStmt.elseClause.accept(this);
        SymTable.popState();
        
        lastType = VoidType.instance;
    }

    @Override
    public void DotVisitor(WhileLoop whileLoop) {
        whileLoop.head.accept(this);
        if (!lastType.equals(BoolType.instance)) {
            throw new TypeError("While loop condition was " + lastType + " instead of bool");
        }
        
        SymTable.pushState();
        whileLoop.body.accept(this);
        SymTable.popState();
        
        lastType = VoidType.instance;
    }

    @Override
    public void DotVisitor(FunctionCall call) {
        ArrayList<Type> argTypes = new ArrayList<Type>(call.arguments.size());
        for (Expr argExpr : call.arguments) {
           argExpr.accept(this);
           argTypes.add(lastType);
        }
        
        checkFunctionCall(call.functionName, argTypes);
    }

    @Override
    public void DotVisitor(UnaryOp unop) {
        unop.operand.accept(this);
        checkFunctionCall(unop.opName, lastType);
    }
    
    @Override
    public void DotVisitor(BinaryOp binop) {
        binop.left.accept(this);
        Type leftType = lastType;
        binop.right.accept(this);
        Type rightType = lastType;
        
        checkFunctionCall(binop.opName, leftType, rightType);
    }
    
    @Override
    public void DotVisitor(IntConst intConst) {
        lastType = IntType.instance;
    }

    @Override
    public void DotVisitor(BoolConst boolConst) {
        lastType = BoolType.instance;
    }
    
    @Override
    public void DotVisitor(Var var) {
        lastType = SymTable.get(var.name);
        if (lastType == null) {
            throw new TypeError("Unknown variable: " + var.name);
        }
    }
    
    private void checkFunctionCall(String funcName, List<Type> givenArgTypes) {
        Type funcType = SymTable.get(funcName);
        
        if (funcType instanceof FunctionType) {
            FunctionType ft = (FunctionType)funcType;
            
            if (ft.argTypes.size() != givenArgTypes.size()) {
                throw new TypeError(funcName + " expects " + ft.argTypes.size() + " arguments but " + givenArgTypes.size() + " given");
            }
            
            for (int i = 0; i < givenArgTypes.size(); i++) {
                Type given = givenArgTypes.get(i);
                Type expected = ft.argTypes.get(i);
                if (!canBeAssigned(given, expected)) {
                    throw new TypeError(funcName + " argument " + (i+1) + " expects " + expected + " but " + given + " given");
                }
            }
            
            lastType = ft.returnType;
        } else {
            throw new TypeError(funcName + " is not a known function or operator");
        }
    }
    
    private void checkFunctionCall(String funcName, Type... givenArgTypes) {
        checkFunctionCall(funcName, Arrays.asList(givenArgTypes));
    }
    
    private boolean canBeAssigned(Type from, Type to) {
        return from.equals(to);
    }
}
}