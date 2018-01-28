module sqat::series1::A2_McCabe

import lang::java::jdt::m3::AST;
import IO;
import List;
import Exception;
import ParseTree;
import util::FileSystem;
import lang::java::\syntax::Disambiguate;
import lang::java::\syntax::Java15;
import analysis::m3::AST;
import analysis::statistics::Frequency;
import analysis::statistics::Correlation;
/*

Construct a distribution of method cylcomatic complexity. 
(that is: a map[int, int] where the key is the McCabe complexity, and the value the frequency it occurs)


Questions:
- which method has the highest complexity (use the @src annotation to get a method's location)
Inky.java ,Mapparser.java->7 (2on implementation)
Inky.java ->8 1st implementation
as i checked inky.java prefer the 7 complexity solution
- how does pacman fare w.r.t. the SIG maintainability McCabe thresholds?
1-10 simple, without much risk(every function)
15% ->++
- is code size correlated with McCabe in this case (use functions in analysis::statistics::Correlation to find out)? 
  (Background: Davy Landman, Alexander Serebrenik, Eric Bouwers and Jurgen J. Vinju. Empirical analysis 
  of the relationship between CC and SLOC in a large corpus of Java methods 
  and C functions Journal of Software: Evolution and Process. 2016. 
  http://homepages.cwi.nl/~jurgenv/papers/JSEP-2015.pdf)
  
  
- what if you separate out the test sources?
370 c final,61 c test sources Biggest LauncherSmokeTest.java complexity 2
378 c final(first implementation)
Tips: 
- the AST data type can be found in module lang::java::m3::AST
- use visit to quickly find methods in Declaration ASTs
- compute McCabe by matching on AST nodes

Sanity checks
- write tests to check your implementation of McCabe

Bonus
- write visualization using vis::Figure and vis::Render to render a histogram.

*/

set[Declaration] jpacmanASTs() = createAstsFromEclipseProject(|project://jpacman-framework|, true); 

alias CC = rel[loc method, int cc];
/*helping function modifies set of declaration ,creates methods
 *for checking in cc complexity function
 *returns @list[Declaration]
*/
list[Declaration] getMethods(Declaration decs){
list[Declaration] methods=[];
visit(decs){
case m:\method(Type \return,str name,list[Declaration] parameters,list[Expression] exceptions,Statement check):methods+=[m];
}return methods;}

/*main function,calculates the complexity of the system,prints the
*final system complexity and returns the max complexity
*@returns cc
*/
CC cc(set[Declaration] decls) {
  CC result = {};
   int max=0;
    CC distribution={};
   loc maxl;
   lrel[int,int] dips=[];
  int final=0;
  for (m<-decls){
  x=getMethods(m);
  for (check<-x){
  resultx = 1;  
  n=0;
      visit (check) {
        case \if(_,_) : resultx += 1;
        case \if(_,_,_) : resultx += 1;
        case \case(_) : resultx += 1;
        case \do(_,_) : resultx += 1;
        case \while(_,_) : resultx += 1;
        case \for(_,_,_) : resultx += 1;
        case \for(_,_,_,_) : resultx += 1;
        case foreach(_,_,_) : resultx += 1;
        case \catch(_,_): resultx += 1;
        case \conditional(_,_,_): resultx += 1;
        case infix(_,"&&",_) : resultx += 1;
        case infix(_,"||",_) : resultx += 1;
        case \n : n+=1;
        
  }
  dips+=[<resultx,n>];
 distribution={<check.src,resultx>};
 println( ccDist(distribution));
  if (max<resultx){
  max=resultx;
  maxl=check;
  }
final=final+resultx;  
  }}
println(final); 
println(covariance(dips));
println(PearsonsCorrelation(dips));
result={<maxl.src,max>};
  return result;
}

alias CCDist = map[int cc, int freq];
/*returns the distribution
*/
CCDist ccDist(CC cc) {
 return distribution(cc);
}
