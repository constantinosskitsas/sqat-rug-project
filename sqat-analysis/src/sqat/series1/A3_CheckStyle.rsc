module sqat::series1::A3_CheckStyle

import String;
import Java17ish;
import Message;
import lang::java::\syntax::Java15;
import List;
import Exception;
import ParseTree;
import util::FileSystem;
import lang::java::\syntax::Disambiguate;
import IO;
import analysis::m3::AST;
import lang::java::m3::Core;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
/*

Assignment: detect style violations in Java source code.
Select 3 checks out of this list:  http://checkstyle.sourceforge.net/checks.html
Compute a set[Message] (see module Message) containing 
check-style-warnings + location of  the offending source fragment. 

Plus: invent your own style violation or code smell and write a checker.

Note: since concrete matching in Rascal is "modulo Layout", you cannot
do checks of layout or comments (or, at least, this will be very hard).

JPacman has a list of enabled checks in checkstyle.xml.
If you're checking for those, introduce them first to see your implementation
finds them.

Questions
- for each violation: look at the code and describe what is going on? 
  Is it a "valid" violation, or a false positive?

Tips 

- use the grammar in lang::java::\syntax::Java15 to parse source files
  (using parse(#start[CompilationUnit], aLoc), in ParseTree)
  now you can use concrete syntax matching (as in Series 0)

- alternatively: some checks can be based on the M3 ASTs.

- use the functionality defined in util::ResourceMarkers to decorate Java 
  source editors with line decorations to indicate the smell/style violation
  (e.g., addMessageMarkers(set[Message]))

  
Bonus:
- write simple "refactorings" to fix one or more classes of violations 

*/	
/*
Checks that there are no import statements that use the * notation.
Rationale: Importing all classes from a package or 
static members from a class leads to tight coupling 
between packages or classes and might lead to problems 
when a new version of a library introduces name clashes.
@return set[Message] info
*/
set[Message] errorStyle1(loc project) {
set[Message] result = {};
locSet = files(project);
 for (i <- locSet) {
 if(i.extension == "java"){
 	stringvar = readFile(i);
if(/(?m)\s*import\s+(\w+\.){1,}\*\;/ :=stringvar)
result+=info("import with * ", i);
}
}return result;
}

/*variables over 15 letter are difficult to use and remember
*final are also included
*@return set[Message]
*/
set[Message] myviolation(loc project) {
set[Message] result = {};
locSet = files(project);
 for (i <- locSet) {
 if(i.extension == "java"){
 	stringvar = readFile(i);
  if(/(?m)(int|char|String)\s+(\w+){15,}\s*\=/ :=stringvar)
result+=info("big variable name,  type violation", i);
}
}return result;
}
/*
Checks if any class or object member is explicitly initialized to default for its type value (null for object references, zero for numeric types and char and false for boolean.

Rationale: Each instance variable gets initialized twice,
 to the same value. Java initializes each instance variable
  to its default value (0 or null) before performing any
initialization specified in the code. So in this case,
 x gets initialized to 0 twice, and bar gets initialized to null
  twice. So there is a minor inefficiency. 
  This style of coding is a holdover from C/C++ style coding,
   and it shows that the developer isn't really confident that
    Java initializes instance variables to default values.
@return set[message]
*/
set[Message] errorStyle2(loc project) {
set[Message] result = {};
locSet = files(project);
 for (i <- locSet) {
 if(i.extension == "java"){
 	stringvar = readFile(i);
 if(/(?m)(\w+)\s+(\w+)\s*\=\s*null\s*\;/ :=stringvar)
result+=info(" A b = null; type violation", i);
 else if(/(?m)(int|char|String)\s+(\w+)\[\]\s*\=\s*null\s*\;/ :=stringvar)
result+=info("int ar1[] = null;  type violation", i);
else if(/(?m)(\w+)\<(\w+)\>\s+(\w+)\s*\=\s*null\s*\;/ :=stringvar)
result+=info("Bar<String> bar = null;   type violation", i);
else if(/(?m)(\w+)\<(\w+)\>\[\]\s+(\w+)\s*\=\s*null\s*\;/ :=stringvar)
result+=info(" Bar<String>[] barArray = null;   type violation", i);
}
}return result;
}

/* Checks cyclomatic complexity against a specified limit.
 It is a measure of the minimum number of possible paths through
  the source and therefore the number of required tests,
   it is not a about quality of code! It is only applied to
    methods, c-tors, static initializers and instance 
    initializers. 
The complexity is equal to the number of decision points + 1
 Decision points: if, while , do, for, ?:, catch , switch, 
 case statements, and operators && and || in the body of target. 
By pure theory level 1-4 is considered easy to test, 5-7 OK,
 8-10 consider re-factoring to ease testing, and 11+ re-factor
  now as testing will be painful. 
When it comes to code quality measurement by this metric
 level 10 is very good level as a ultimate target 
 (that is hard to archive). 
@return set[Message]
*/
//int magkas(MethodDec x) {//mccabe for exercise2
set[Message] errorStyle3(MethodDec x) {
set[Message] result = {};
int com=1;
int count=0;
m=x;
  visit (m) {
  
    case (Stm)`do <Stm _> while (<Expr _>);`: com += 1;
    case (Stm)`while (<Expr _>) <Stm _>`: com += 1;
    case (Stm)`if (<Expr _>) <Stm _>`: com +=1;
    case (Stm)`if (<Expr _>) <Stm _> else <Stm _>`: com +=1;
    case (Stm)`for (<{Expr ","}* _>; <Expr? _>; <{Expr ","}*_>) <Stm _>` : com += 1;
    case (Stm)`for (<LocalVarDec _> ; <Expr? e> ; <{Expr ","}* _>) <Stm _>`: com += 1;
    case (Stm)`for (<FormalParam _> : <Expr _>) <Stm _>` : com += 1;
    case (Stm)`switch (<Expr _> ) <SwitchBlock _>`: com += 1;
    case (SwitchLabel)`case <Expr _> :` : com += 1;
    case (CatchClause)`catch (<FormalParam _>) <Block _>` : com += 1;
  };
  
  if (com>6)
  result+=info("complexity over 6 ", m@\loc);
return result;
}/*
Detects empty statements (standalone ";" semicolon).
@return set[Message]
*/
set[Message] errorStyle4(MethodDec x) {
set[Message] result = {};

m=x;
  visit (m) {
  case (Stm)`do ; while (<Expr _>);`: result+=info("empty statement1 ", m@\loc);
    case (Stm)`while (<Expr _>) ;`: result+=info("empty statement2 ", m@\loc);
    case (Stm)`if (<Expr _>) ;`: result+=info("empty statement3 ", m@\loc);
    case (Stm)`if (<Expr _>) <Stm _> else ;`: result+=info("empty statement4 ", m@\loc);
    case (Stm)`if (<Expr _>) ; else <Stm _>`: result+=info("empty statement5 ", m@\loc);
    case (Stm)`for (<{Expr ","}* _>; <Expr? _>; <{Expr ","}*_>) ;` : result+=info("empty statement6 ", m@\loc);
    case (Stm)`for (<LocalVarDec _> ; <Expr? e> ; <{Expr ","}* _>) ;`: result+=info("empty statement7 ", m@\loc);
    case (Stm)`for (<FormalParam _> : <Expr _>) ;` : result+=info("empty statement9 ", m@\loc);
  };
 
return result;
}
set[Message] checkStyle(loc project) {
  set[Message] result = {};
 	result2=[*emptystatement(f) | /file(f) <- crawl(project), f.extension == "java"];
 	result1 = [*maxCC(f) | /file(f) <- crawl(project), f.extension == "java"];
 result1=result1+result2+errorStyle2(project)+errorStyle1(project)+myviolation(project);
  for (i <- result1) { 
  if(i=={});
else result+=i;
}/* mccabe check for exercise 2
time=0;
for (i <- result1) 
 time=time+i;
println(time);*/
  return result;
}
set[MethodDec] allMethods(loc file) 
  = {m | /MethodDec m := parse(#start[CompilationUnit], file,allowAmbiguity=true)};

//list[int] maxCC(loc file) //mccabe for exercise2
list[set[Message]] maxCC(loc file) 
  = [errorStyle3(m) | m <- allMethods(file)];
  
list[set[Message]] emptystatement(loc file) 
  = [errorStyle4(m) | m <- allMethods(file)];
  
 