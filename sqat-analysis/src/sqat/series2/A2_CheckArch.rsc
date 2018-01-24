module sqat::series2::A2_CheckArch

import sqat::series2::Dicto;
import lang::java::jdt::m3::Core;
import Message;
import ParseTree;
import IO;
import lang::java::m3::Core;
import analysis::m3::Core;
import Plugin;
import String;
import util::FileSystem;
import Java17ish;
import Set;
import String;
import Boolean;
/*

This assignment has two parts:
- write a dicto file (see example.dicto for an example)
  containing 3 or more architectural rules for Pacman
  
- write an evaluator for the Dicto language that checks for
  violations of these rules. 

Part 1  

An example is: ensure that the game logic component does not 
depend on the GUI subsystem. Another example could relate to
the proper use of factories.   

Make sure that at least one of them is violated (perhaps by
first introducing the violation).

Explain why your rule encodes "good" design.
  
Part 2:  
 
Complete the body of this function to check a Dicto rule
against the information on the M3 model (which will come
from the pacman project). 

A simple way to get started is to pattern match on variants
of the rules, like so:

switch (rule) {
  case (Rule)`<Entity e1> cannot depend <Entity e2>`: ...
  case (Rule)`<Entity e1> must invoke <Entity e2>`: ...
  ....
}

Implement each specific check for each case in a separate function.
If there's a violation, produce an error in the `msgs` set.  
Later on you can factor out commonality between rules if needed.

The messages you produce will be automatically marked in the Java
file editors of Eclipse (see Plugin.rsc for how it works).

Tip:
- for info on M3 see series2/A1a_StatCov.rsc.

Questions
- how would you test your evaluator of Dicto rules? (sketch a design)
- come up with 3 rule types that are not currently supported by this version
  of Dicto (and explain why you'd need them).
System can not contain cycles
Only test can contain dead methods
implementation  class must have interface named the same with class without implementation 
run:
  import sqat::series2::A2_CheckArch;
  import sqat::series2::Dicto;
  import ParseTree;
  import lang::java::jdt::m3::Core;
  M3 m3=createM3FromEclipseProject(|project://jpacman-framework|);
  pt = parse(#start[Dicto], |project://sqat-analysis/src/sqat/series2/aRules.dicto|);
  eval(pt, m3);
  General comments.
  I will explain analytical every function,line by line due the offline evaluation
  Rule 1
Test classes must import org.junit.Test
Test classes are suposed to be test and in this case Junit
Helps to easy maintain the code .

Rule 2
Non test classes  cannot import org.junit.Test
We cannot have in main classes test,test have to be seperated.
Test have to implemented in different location.
Helps to easy maintain the code .

  
  Rule 3
  Logic of the program has not to be depended with UI 
  also game has not to be dependend on sprite
  Its good to seperate and each package to do different job 
*/


set[Message] eval(start[Dicto] dicto, M3 m3) = eval(dicto.top, m3);

set[Message] eval((Dicto)`<Rule* rules>`, M3 m3) 
  = ( {} | it + eval(r, m3) | r <- rules );
  
  M3 jpacmanM3() = createM3FromEclipseProject(|project://jpacman-framework|);
  /** evaluates the rules and call the function
  *@return set[Message]
  */
set[Message] eval(Rule rule, M3 m3) {
  set[Message] msgs = {};
  
  switch (rule) {
  case (Rule)`<Entity e1> must import <Entity e2>`: msgs+=CheckMustImportJTest(m3,e1,e2);
  case (Rule)`<Entity e1> cannot import <Entity e2>`: msgs+=ClassNotImportJTest(m3,e1,e2);
  case (Rule)`<Entity e1> cannot depend <Entity e2>`:msgs+=checkNotdepend(m3,e1,e2);
}
  return msgs;
}
set[str] getImports(loc javafile){
	set[str] imports = {};
	start[CompilationUnit] tree = parseJava(javafile);
	visit(tree){
		case (ImportDec)`import <TypeName t> ;` : imports += unparse(t);
	};
	return imports;
}
/*Checks the rule 2 .replaceAll so it can be location,i add .java because i only care 
about classes,i want the imports of specific classes.After our first evaluation i used
containement to work with complication unit so i can take the imports easily.i only work with
one class every time and not with package so i will have only one complication unit per time
so, i have loc instead of set[loc] after i get the complication unit.Then I itterate due the 
imports to check if contains e2
*@returns set[Message]
*/
set[Message] ClassNotImportJTest(M3 m3,Entity e1, Entity e2){
 set[Message] msgs = {};
	e1Loc = "/" + replaceAll("<e1>", ".", "/");
	entity2 = "<e2>";
	e1Loc+=".java";
	loc complic;
	everything=m3.containment;
	 imports={};	 
	for(i<-everything)
	if(isCompilationUnit(i.from))
	if(contains(i.from.path, e1Loc))
	complic=i;
	imports=getImports(complic.from);	
	for (importC<-imports)
		if(contains(importC, entity2))
			msgs+= warning("<e1> cannot not import <e2>", complic.from);
return msgs;}

/*Checks the rule 1 .replaceAll so it can be location,i add .java because i only care 
about classes,i want the imports of specific classes.After our first evaluation i used
containement to work with complication unit so i can take the imports easily.i only work with
one class every time and not with package so i will have only one complication unit per time
so, i have loc instead of set[loc] after i get the complication unit.Then I itterate due the 
imports to check if contains e2
*@returns set[Message]
*/
set[Message] CheckMustImportJTest(M3 m3,Entity e1, Entity e2){
 set[Message] msgs = {};
	e1Loc = "/" + replaceAll("<e1>", ".", "/");
	entity2 = "<e2>";
	e1Loc+=".java";
	everything=m3.containment;
	 x1={};
	 loc complic;
	 bool error=false;
	for(i<-everything)
	if(isCompilationUnit(i.from))
	if(contains(i.from.path, e1Loc))
	complic=i;
	error=false;
	imports=getImports(complic.from);
	for (importC<-imports)
		if(contains(importC, entity2))
		error=true;
		if (error==false)
			msgs+= warning("<e1> must import <e2>", complic.from);
return msgs;}


/*Checks the rule 3.Replace all to take the location i want to test for both entities.
I got the dependencies from m3.typeDependency and i itterate to all of them.
If they contain entity 1 and entity 2 [from,to] there is a violation and i return 
warning message
*@returns set[Message]
*/
set[Message] checkNotdepend(M3 m3,Entity e1, Entity e2){
set[Message] msgs = {}; 
e1Loc = "/" + replaceAll("<e1>", ".", "/");
e2loc=  "/" + replaceAll("<e2>", ".", "/");
	dependencies=m3.typeDependency;
	for (i<-dependencies)
	if(contains(i.from.path, e1Loc) && contains(i.to.path, e2loc))
	msgs+=warning("<e1> cannot depend on <e2>", i.from);
 	
	
return msgs;}

