module sqat::series2::A1a_StatCov
import Set;
import lang::java::jdt::m3::Core;
import analysis::graphs::Graph;
import lang::java::jdt::m3::AST;
import IO;
import List;
import Exception;
import ParseTree;
import util::FileSystem;
import lang::java::\syntax::Disambiguate;
import lang::java::\syntax::Java15;
import analysis::m3::AST;
import Number;
import util::Math;
/*

Implement static code coverage metrics by Alves & Visser 
(https://www.sig.eu/en/about-sig/publications/static-estimation-test-coverage)


The relevant base data types provided by M3 can be found here:

- module analysis::m3::Core:

rel[loc name, loc src]        M3.declarations;            // maps declarations to where they are declared. contains any kind of data or type or code declaration (classes, fields, methods, variables, etc. etc.)
rel[loc name, TypeSymbol typ] M3.types;                   // assigns types to declared source code artifacts
rel[loc src, loc name]        M3.uses;                    // maps source locations of usages to the respective declarations
rel[loc from, loc to]         M3.containment;             // what is logically contained in what else (not necessarily physically, but usually also)
list[Message]                 M3.messages;                // error messages and warnings produced while constructing a single m3 model
rel[str simpleName, loc qualifiedName]  M3.names;         // convenience mapping from logical names to end-user readable (GUI) names, and vice versa
rel[loc definition, loc comments]       M3.documentation; // comments and javadoc attached to declared things
rel[loc definition, Modifier modifier] M3.modifiers;     // modifiers associated with declared things

- module  lang::java::m3::Core:

rel[loc from, loc to] M3.extends;            // classes extending classes and interfaces extending interfaces
rel[loc from, loc to] M3.implements;         // classes implementing interfaces
rel[loc from, loc to] M3.methodInvocation;   // methods calling each other (including constructors)
rel[loc from, loc to] M3.fieldAccess;        // code using data (like fields)
rel[loc from, loc to] M3.typeDependency;     // using a type literal in some code (types of variables, annotations)
rel[loc from, loc to] M3.methodOverrides;    // which method override which other methods
rel[loc declaration, loc annotation] M3.annotations;

Tips
- encode (labeled) graphs as ternary relations: rel[Node,Label,Node]
- define a data type for node types and edge types (labels) 
- use the solve statement to implement your own (custom) transitive closure for reachability.

Questions:
- what methods are not covered at all?
mostly get methods and UI,sprite 
- how do your results compare to the jpacman results in the paper? Has jpacman improved?
JPacMan 88.06% 93.53% −5.47% at system level (paper)
JpacMan 89.91% 81.7    -0.8 (my code and clover)
- use a third-party coverage tool (e.g. Clover) to compare your results to (explain differences)
 Results static and clover coverage are highly correlated.The differences from true coverages is
 Branch coverage
Branch coverage (or 'decision coverage') is a code coverage metric that measures 
which possible branches in flow control structures are followed. 
Clover does this by recording if the boolean expression in the control structure 
evaluated to both true and false during execution.

Statement coverage
Statement coverage is a code coverage metric that measures which statements in a 
body of code have been executed through a test run, and which statements have not.
Method coverage
Method coverage is a code coverage metric that measures whether a method was 
entered at all during execution.

On the other hand static coverage works on source code
*/




M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework|);

alias Graph = rel[loc from, loc to];
/**
*Takes the M3 model and create graph
@returns graph
*/
Graph creategraph(M3 mymodel) {
Graph graph = mymodel.implements;
graph+=mymodel.methodInvocation;
graph+=mymodel.extends;
graph+=mymodel.methodOverrides;
i=classes(mymodel);
i+=methods(mymodel);
i+=interfaces(mymodel);
i+=packages(mymodel);
i+=constructors(mymodel);
for (x<-i)
graph+={<x,x>};
return graph;
}

/**takes the M3 model and counts number of classes,interfaces,package etc for the result
*@returns int size 
*/
int count(M3 m){
//if (isMethod(decs.name)||isPackage(decs.name)|| isClass(decs.name)||isCompilationUnit(decs.name))
x=classes(m);
x+=interfaces(m);
x+=packages(m);
x+=methods(m);
x+=constructors(m);
//x+=compilationUnit(m);
return size(x);
}/*
@memo public set[loc] classes(M3 m) =  {e | <e,_> <- m.declarations, isClass(e)};
@memo public set[loc] interfaces(M3 m) =  {e | <e,_> <- m.declarations, isInterface(e)};
@memo public set[loc] packages(M3 m) = {e | <e,_> <- m.declarations, isPackage(e)};
@memo public set[loc] methods(M3 m) = {e | <e,_> <- m.declarations, isMethod(e)};
@memo public set[loc] constructors(M3 m) = {e | <e,_> <- m.declarations, isConstructor(e)};
*/
/*finds all the test files to seach for coverage in graph
*@returns list[loc]
*/
list[loc] findTest(M3 mymodel) {
testsc=[];
mymodel1=mymodel.declarations;
str testpath="as";
for (decs<-mymodel1){
testpath=decs.src.path;
if(/(?m)\/src\/test/ := testpath){
if (isMethod(decs.name)||isPackage(decs.name)|| isClass(decs.name))
//||isCompilationUnit(decs.name)
testsc+=decs.name;
}
}return testsc;
}
/*
public bool isCompilationUnit(loc entity) = entity.scheme == "java+compilationUnit";
public bool isPackage(loc entity) = entity.scheme == "java+package";
public bool isClass(loc entity) = entity.scheme == "java+class";
public bool isMethod(loc entity) = entity.scheme == "java+method" || entity.scheme == "java+constructor" || entity.scheme == "java+initializer";
*/

/*main function to test static coverage,calls create graph,findTest,count
*reach returns the set that test covers returns the final coverage 
*returns real 
*/
real staticoverage(M3 mymodel){
Graph grafos = creategraph(mymodel);
testc=findTest(mymodel);
set[loc] coveredS={};
tests=toSet(testc);
coveredS=reach(grafos,tests);
coveredA=size(coveredS);
allin=count(mymodel);
println(size(testc));
println(coveredA);
real  coveredR=coveredA/1.0;
real coverageR=coveredR/allin;
println(allin);
notcovered(mymodel,coveredS);
return (coverageR*100);//%80.91
}
/*finds and prints the not covered methods
@return void
*/
void notcovered(M3 model,set[loc] coveredS){
methodes=methods(model);
println(size(methodes));
set[loc] notcoveredm={};
notcoveredm=methodes-coveredS;
//println(size(notcoveredm));
real  coveredR=(size(methodes)-size(notcoveredm))/1.0;
real coverageR=coveredR/size(methodes);
//println((coverageR*100));
for (print<-notcoveredm);
//println(print);
}