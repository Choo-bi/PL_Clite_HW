import java.util.*;

public class Parser {
    // Recursive descent parser that inputs a C++Lite program and 
    // generates its abstract syntax.  Each method corresponds to
    // a concrete syntax grammar rule, which appears as a comment
    // at the beginning of the method.
  
    Token token;          // current token from the input stream
    Lexer lexer;

    public Parser(Lexer ts) { // Open the C++Lite source program
        lexer = ts;                          // as a token stream, and
        token = lexer.next();            // retrieve its first Token
    }
  
    private String match (TokenType t) {
        String value = token.value();
        System.out.println(token.type() + " " + token.value());
        if (token.type().equals(t))
            token = lexer.next();
        else
            error(t);
        return value;
    }

    private void error(TokenType tok) {
        System.err.println("Syntax error: expecting: " + tok 
                           + "; saw: " + token);
        System.exit(1);
    }
  
    private void error(String tok) {
        System.err.println("Syntax error: expecting: " + tok 
                           + "; saw: " + token);
        System.exit(1);
    }
  
    public Program program() {
        // Program --> void main ( ) '{' Declarations Statements '}'
        TokenType[ ] header = {TokenType.Int, TokenType.Main,
                          TokenType.LeftParen, TokenType.RightParen};
        for (int i=0; i<header.length; i++)   // bypass "int main ( )"
            match(header[i]);
        match(TokenType.LeftBrace);
        Declarations dec = declarations();
        Block bl = statements();
        match(TokenType.RightBrace);
        return new Program(dec,bl);  // student exercise
    }
  
    private Declarations declarations () {
        // Declarations --> { Declaration }
        Declarations dec = new Declarations();
        while (isType()) {
            declaration(dec);
        }
        return dec;
    }
  
    private void declaration (Declarations ds) {
        // Declaration  --> Type Identifier { , Identifier } ;
        Type t = type();
        Variable v = new Variable(match(TokenType.Identifier));
        Declaration d = new Declaration(v, t);
        ds.add(d);
        while(token.type().equals(TokenType.Comma)){
            match(TokenType.Comma);
            v = new Variable(match(TokenType.Identifier));
            d = new Declaration(v,t);
            ds.add(d);
        }
        match(TokenType.Semicolon);
    }
  
    private Type type () {
        // Type  -->  int | bool | float | char 
        Type t = null;
        if (token.type() == TokenType.Int)
            t = Type.INT;
        else if (token.type() == TokenType.Bool)
            t = Type.BOOL;
        else if (token.type() == TokenType.Float)
            t = Type.FLOAT;
        else if (token.type() == TokenType.Char)
            t = Type.CHAR;
        else
            error("int | bool | float | char");
        token = lexer.next();
        return t;          
    }

    private Statement statement() {
        // Statement --> ; | Block | Assignment | IfStatement | WhileStatement | Call
        Statement s=null;
        if(token.type().equals(TokenType.Semicolon))
            s = new Skip(); //semicolon
        else if(token.type().equals(TokenType.LeftBrace)){
            match(TokenType.LeftBrace);
            s = statements();
            match(TokenType.RightBrace);
        }
        else if(token.type().equals(TokenType.Identifier)){
            s = assignment();
        }
        else if(token.type().equals(TokenType.If)){
            s= ifStatement();
        }
        else if(token.type().equals(TokenType.While)){
            s= whileStatement();
        }
        else{
            error(token.type());
        }
        // student exercise
        return s;
    }
  
    private Block statements () {
        // Block --> '{' Statements '}'
        Block b = new Block();
        while(!token.type().equals(TokenType.RightBrace)) {
            Statement s = statement();
            b.members.add(s);
        }
        return b;
    }
  
    private Assignment assignment () {
        // Assignment --> Identifier = Expression ;
        Variable target = new Variable(match(TokenType.Identifier));
        match(TokenType.Assign);
        Expression source = expression();
        match(TokenType.Semicolon);
        return new Assignment(target, source);
    }
  
    private Conditional ifStatement () {
        // IfStatement --> if ( Expression ) Statement [ else Statement ]
        match(TokenType.If);
        match(TokenType.LeftParen);
        Expression ex = expression();
        match(TokenType.RightParen);
        Statement consequent = statement();
        if (token.type().equals(TokenType.Else)) {
            match(TokenType.Else);
            Statement alternative = statement();
            return new Conditional(ex, consequent, alternative);
        } else {
            return new Conditional(ex, consequent);
        }
    }
  
    private Loop whileStatement () {
        // WhileStatement --> while ( Expression ) Statement
        match(TokenType.While);
        match(TokenType.LeftParen);
        Expression ex = expression();
        match(TokenType.RightParen);
        Statement body = statement();
        return new Loop(ex, body);
    }

    private Expression expression () {
        // Expression --> Conjunction { || Conjunction }
        Expression e = conjunction();
        while (token.type().equals(TokenType.Or)) {
            Operator op = new Operator(match(TokenType.Or));
            Expression term2 = conjunction();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression conjunction () {
        // Conjunction --> Equality { && Equality }
        Expression e = equality();
        while (token.type().equals(TokenType.And)) {
            Operator op = new Operator(match(TokenType.And));
            Expression term2 = equality();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression equality () {
        // Equality --> Relation [ EquOp Relation ]
        Expression e = relation();
        while (isEqualityOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = relation();
            e = new Binary(op, e, term2);
        }
        return e;
    }

    private Expression relation (){
        // Relation --> Addition [RelOp Addition] 
        Expression e = addition();
        while (isRelationalOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = addition();
            e = new Binary(op, e, term2);
        }
        return e;// student exercise
    }
  
    private Expression addition () {
        // Addition --> Term { AddOp Term }
        Expression e = term();
        while (isAddOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = term();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression term () {
        // Term --> Factor { MultiplyOp Factor }
        Expression e = factor();
        while (isMultiplyOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term2 = factor();
            e = new Binary(op, e, term2);
        }
        return e;
    }
  
    private Expression factor() {
        // Factor --> [ UnaryOp ] Primary 
        if (isUnaryOp()) {
            Operator op = new Operator(match(token.type()));
            Expression term = primary();
            return new Unary(op, term);
        }
        else return primary();
    }
  
    private Expression primary () {
        // Primary --> Identifier | Literal | ( Expression )
        //             | Type ( Expression )
        Expression e = null;
        if (token.type().equals(TokenType.Identifier)) {
            e = new Variable(match(TokenType.Identifier));
        } else if (isLiteral()) {
            e = literal();
        } else if (token.type().equals(TokenType.LeftParen)) {
            token = lexer.next();
            e = expression();       
            match(TokenType.RightParen);
        } else if (isType( )) {
            Operator op = new Operator(match(token.type()));
            match(TokenType.LeftParen);
            Expression term = expression();
            match(TokenType.RightParen);
            e = new Unary(op, term);
        } else error("Identifier | Literal | ( | Type");
        return e;
    }

    private Value literal( ) {
        Value v = null;
        if(token.type().equals(TokenType.FloatLiteral)){
            v = new FloatValue(Float.parseFloat(token.value()));
            match(TokenType.FloatLiteral);
        }
        else if(token.type().equals(TokenType.IntLiteral)){
            v = new  IntValue(Integer.parseInt(token.value()));
            match(TokenType.IntLiteral);

        }
        else if(token.type().equals(TokenType.CharLiteral)){
            v= new CharValue((token.value().charAt(0)));
            match(TokenType.CharLiteral);
        }
        else if(token.value()== "true"){
            v = new BoolValue(true);
            match(TokenType.True);
        }
        else if(token.value() == "false"){
            v = new BoolValue(false);
            match(TokenType.False);
        }
        else
            error(token.type());

        return v;
                // student exercise
    }
  

    private boolean isAddOp( ) {
        return token.type().equals(TokenType.Plus) ||
               token.type().equals(TokenType.Minus);
    }
    
    private boolean isMultiplyOp( ) {
        return token.type().equals(TokenType.Multiply) ||
               token.type().equals(TokenType.Divide);
    }
    
    private boolean isUnaryOp( ) {
        return token.type().equals(TokenType.Not) ||
               token.type().equals(TokenType.Minus);
    }
    
    private boolean isEqualityOp( ) {
        return token.type().equals(TokenType.Equals) ||
            token.type().equals(TokenType.NotEqual);
    }
    
    private boolean isRelationalOp( ) {
        return token.type().equals(TokenType.Less) ||
               token.type().equals(TokenType.LessEqual) || 
               token.type().equals(TokenType.Greater) ||
               token.type().equals(TokenType.GreaterEqual);
    }
    
    private boolean isType( ) {
        return token.type().equals(TokenType.Int)
            || token.type().equals(TokenType.Bool) 
            || token.type().equals(TokenType.Float)
            || token.type().equals(TokenType.Char);
    }
    
    private boolean isLiteral( ) {
        return token.type().equals(TokenType.IntLiteral) ||
            isBooleanLiteral() ||
            token.type().equals(TokenType.FloatLiteral) ||
            token.type().equals(TokenType.CharLiteral);
    }
    
    private boolean isBooleanLiteral( ) {
        return token.type().equals(TokenType.True) ||
            token.type().equals(TokenType.False);
    }

    public static void main(String args[]) {
        Parser parser  = new Parser(new Lexer(args[0]));
        Program prog = parser.program();
        prog.display(0);           // display abstract syntax tree
    } //main

} // Parser
