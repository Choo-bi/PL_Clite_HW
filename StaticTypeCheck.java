// StaticTypeCheck.java

import java.util.*;

// Static type checking for Clite is defined by the functions 
// V and the auxiliary functions typing and typeOf.  These
// functions use the classes in the Abstract Syntax of Clite.


public class StaticTypeCheck {

    public static TypeMap typing (Declarations d) {
        TypeMap map = new TypeMap();
        for (Declaration di : d)
            map.put (di.v, di.t);
        return map;
    }
    public static TypeMap typing (Declarations d, Functions f) {
        TypeMap map = new TypeMap();
        for (int i = 0; i < d.size(); i++){
            Declaration di = (Declaration)(d.get(i));
            map.put (di.v, di.t);
        }
        for (int i = 0; i < f.size(); i++){
            Function fi = (Function)f.get(i);
            map.put (new Variable (fi.id),new ProtoType (fi.t, fi.params));
        }
        return map;
    }
    public static void check(boolean test, String msg) {
        if (test)  return;
        System.err.println(msg);
        System.exit(1);
    }
    public static void checkProtoType (ProtoType p, TypeMap tm, Type t, Expressions es) {
        TypeMap tmp = typing(p.params); // temporary type map for params
        check (p.equals(t), "calls can only be to void functions");
        check (es.size() == p.params.size(),"match numbers of arguments and params");
        for (int i=0; i<es.size(); i++) {
            // match arg types with param types
            Expression e = (Expression)es.get(i);
            Expression e2 = (Expression)((Declaration)p.params.get(i)).v;
            check(typeOf(e, tm).equals(typeOf(e2, tmp)),"argument type does not match parameter");
        }
    }
    public static void V (Declarations d) {
        for (int i=0; i<d.size() - 1; i++)
            for (int j=i+1; j<d.size(); j++) {
                Declaration di = d.get(i);
                Declaration dj = d.get(j);
                check( ! (di.v.equals(dj.v)),
                        "duplicate declaration: " + dj.v);
            }
    }

    public static void V (Program p) {
        V (p.globals, p.functions);
        boolean foundmain = false;
        TypeMap tmg = typing(p.globals, p.functions); // global TypeMap
        //System.out.print ("Globals = "); p.globals.display(1);
        for (Function f : p.functions) {
            if (f.id.equals("main"))
                if (foundmain)
                    check(false, "Duplicate main function");
                else
                    foundmain = true;
            V(f.params, f.locals);
            TypeMap tmf = typing(f.params).onion(typing(f.locals));
            tmf = tmg.onion(tmf);
            //System.out.print ("\nFunction " + f.id + " = ");tmf.display();
            V(f.body, tmf);
        }
    }
    public static void V (Declarations ds, Functions fs) {
        for (int i = 0; i < ds.size(); i++) {
            Declaration di = ds.get(i);
            for (int j = i + 1; j < ds.size(); j++) {
                Declaration dj = ds.get(j);
                check (! di.v.equals(dj.v), "duplicate declaration: " + dj.v);
            }
            for (int j = 0; j < fs.size(); j++) {
                Function fj = fs.get(j);
                check (! di.v.toString().equals(fj.id),"duplicate declaration: " + fj.id);
            }
        }
    }
    public static void V (Declarations ds1, Declarations ds2) {
        for (int i = 0; i < ds1.size(); i++) {
            Declaration di = ds1.get(i);
            for (int j = 0; j < ds2.size(); j++) {
                Declaration dj = ds2.get(j);
                check (! di.v.equals(dj.v), "duplicate declaration: " + dj.v);
            }
        }
    }
    public static Type typeOf (Function f, TypeMap tm) {
        Variable v = new Variable(f.id);
        check(tm.containsKey(v), "undefined variable: " + v);
        return tm.get(v);  // returns ProtoType
    }
    public static Type typeOf (Expression e, TypeMap tm) {
        if (e instanceof Value) return ((Value)e).type;
        if (e instanceof Call) {
            Call ec = (Call)e;
            check(tm.containsKey(new Variable(ec.name)), "undefined name: " + ec.name);
            return tm.get(new Variable(ec.name));  // returns a ProtoType
        }

        if (e instanceof Variable) {
            Variable v = (Variable)e;
            check (tm.containsKey(v), "undefined variable: " + v);
            return (Type) tm.get(v);
        }
        if (e instanceof Binary) {
            Binary b = (Binary)e;
            if (b.op.ArithmeticOp( ))
                if (typeOf(b.term1,tm).equals(Type.FLOAT))
                    return (Type.FLOAT);
                else return (Type.INT);
            if (b.op.RelationalOp( ) || b.op.BooleanOp( ))
                return (Type.BOOL);
        }
        if (e instanceof Unary) {
            Unary u = (Unary)e;
            if (u.op.NotOp( ))        return (Type.BOOL);
            else if (u.op.NegateOp( )) return typeOf(u.term,tm);
            else if (u.op.intOp( ))    return (Type.INT);
            else if (u.op.floatOp( )) return (Type.FLOAT);
            else if (u.op.charOp( ))  return (Type.CHAR);
        }
        throw new IllegalArgumentException("should never reach here");
    }

    public static void V (Expression e, TypeMap tm) {
        if (e instanceof Value)
            return;
        if (e instanceof Variable) {
            Variable v = (Variable)e;
            check( tm.containsKey(v)
                    , "undeclared variable: " + v);
            return;
        }
        if (e instanceof Binary) {
            Binary b = (Binary) e;
            Type typ1 = typeOf(b.term1, tm);
            Type typ2 = typeOf(b.term2, tm);
            V (b.term1, tm);
            V (b.term2, tm);
            if (b.op.ArithmeticOp( ))
                check( typ1.equals(typ2) &&
                                (typ1.equals(Type.INT) || typ1.equals(Type.FLOAT))
                        , "type error for " + b.op);
            else if (b.op.RelationalOp( ))
                check( typ1.equals(typ2) , "type error for " + b.op);
            else if (b.op.BooleanOp( ))
                check( typ1.equals(Type.BOOL) && typ2.equals(Type.BOOL),
                        b.op + ": non-bool operand");
            else
                throw new IllegalArgumentException("Binary V error");
            return;
        }
        if (e instanceof Call) {
            Variable v = new Variable(((Call)e).name);
            Expressions es = ((Call)e).args;
            check(tm.containsKey(v), "undeclared function: " + v);
            ProtoType p = (ProtoType)tm.get(v);
            // check return type and arguments against the ProtoType
            checkProtoType(p, tm, typeOf(e, tm), es);
            return;
        }
        if(e instanceof Unary) {
            Unary u = (Unary)e;
            Type typ = typeOf(u.term,tm);
            V(u.term, tm);
            if(u.op.NotOp()){
                check(typ.equals(Type.BOOL), "type error for " +u.op);
            }
            else if(u.op.NegateOp()){
                check( typ.equals(Type.INT) || typ.equals(Type.FLOAT),"type error for "+u.op);
            }
            else if(u.op.equals(Operator.FLOAT)){
                check(typ.equals(Type.INT), "non-int operand");
            }
            else if(u.op.equals(Operator.INT)){
                check(typ.equals(Type.FLOAT) || typ.equals(Type.CHAR), "type error for ");
            }
            else if(u.op.equals(Operator.CHAR)){
                check(typ.equals(Type.INT), "non-int operand");
            }
            else
                throw new IllegalArgumentException("Unary V error");
            return;
        }
        // student exercise
        throw new IllegalArgumentException("should never reach here");
    }

    public static void V (Statement s, TypeMap tm) {
        if ( s == null )
            throw new IllegalArgumentException( "AST error: null statement");
        if (s instanceof Skip) return;
        if (s instanceof Assignment) {
            Assignment a = (Assignment)s;
            check( tm.containsKey(a.target)
                    , " undefined target in assignment: " + a.target);
            V(a.source, tm);
            Type ttype = (Type)tm.get(a.target);
            Type srctype = typeOf(a.source, tm);
            if (!ttype.equals(srctype)) {
                if (ttype.equals(Type.FLOAT))
                    check( srctype.equals(Type.INT)
                            , "mixed mode assignment to " + a.target);
                else if (ttype.equals(Type.INT))
                    check( srctype.equals(Type.CHAR)
                            , "mixed mode assignment to " + a.target);
                else
                    check( false
                            , "mixed mode assignment to " + a.target);
            }
            return;
        }
        if(s instanceof Conditional){
            Conditional c = (Conditional)s;
            V(c.test, tm);
            Type ttType = typeOf(c.test, tm);
            check(ttType.equals(Type.BOOL), "conditional isn't reasonable");
            V(c.thenbranch, tm);
            V(c.elsebranch, tm);
            return;
        }
        if (s instanceof Loop){
            Loop l = (Loop)s;
            V(l.test, tm);
            Type ttType = typeOf(l.test, tm);
            check(ttType.equals(Type.BOOL), "Loop isn't reasonable");
            V(l.body, tm);
            return;
        }
        if (s instanceof Block){
            Block b = (Block)s;
            for(Statement st : b.members){
                V(st, tm);
            }
            return;
        }
        if (s instanceof Call) {
            Variable v = new Variable(((Call)s).name);
            Expressions es = ((Call)s).args;
            check(tm.containsKey(v), "undefined function: " + v);
            ProtoType p = (ProtoType)tm.get(v);
            checkProtoType(p, tm, Type.VOID, es);
            return;
        }
        if (s instanceof Return) {
            Variable fid = ((Return)s).target;
            check(tm.containsKey(fid), "undefined function: " + fid);
            V(((Return)s).result, tm);
            check (((Type)tm.get(fid)).equals (typeOf(((Return)s).result, tm)),"incorrect return type");
            return;
        }
        // student exercise
        throw new IllegalArgumentException("should never reach here");
    }

    public static void main(String args[]) {
        Parser parser  = new Parser(new Lexer(args[0]));
        Program prog = parser.program();
        prog.display(0);           // student exercise
        System.out.println("\nBegin type checking...");
        System.out.println("Type map:");
        TypeMap map = typing(prog.decpart);
        map.display();   // student exercise
        V(prog);
    } //main

} // class StaticTypeCheck
