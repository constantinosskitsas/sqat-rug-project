module sqat::series1::A1_SLOC

import IO;
import ParseTree;
import String;
import List;
import util::FileSystem;
import sqat::series1::Comments;
/* 

Count Source Lines of Code (SLOC) per file:
- ignore comments
- ignore empty lines

Tips
- use locations with the project scheme: e.g. |project:///jpacman/...|
- functions to crawl directories can be found in util::FileSystem
- use the functions in IO to read source files

Answer the following questions:
- what is the biggest file in JPacman?
Level.java
- what is the total size of JPacman?
2458-tested with software same results.
- is JPacman large according to SIG maintainability? 
small
- what is the ratio between actual code and test code size?
(1902:557) apro (3.41:1)

Sanity checks:
- write tests to ensure you are correctly skipping multi-line comments
- and to ensure that consecutive newlines are counted as one.
- compare you results to external tools sloc and/or cloc.pl

Bonus:
- write a hierarchical tree map visualization using vis::Figure and 
  vis::Render quickly see where the large files are. 
  (https://en.wikipedia.org/wiki/Treemapping) 

*/

/**
	 *  It captures that type of mistake that can have line comment with a star.
	 *So calculation will close before the end of the actual comment.
	 *We capture that if close multiline comments are more than the begin comments
	 * @return The correct end list
	 */
list[int] MultilineMistake(list[int] begin,list[int] end){
if ((size(begin))!=(size(end))){
 	int q=0;
 	int count=0;
 	if(size(end)==2){
 	end=delete(end,0);
 	return end;
 	}else{
 		tend=delete(end,0);
 	tbegin=delete(begin,0);
 	for(int n <- testyi){
 	if(top(tend)<n){
 	end=delete(end,count);
 	break;}
 	count=count+1;
 	if (count==size(tbegin))
 	end=delete(end,count);
 	}}}
 		return end;}
 		
 	/**
	 *  Counts multiline type comments
	 *@return clinescount
	 */	
int countMLines(list[int] begin,list[int] end,str sourcecode){
int clinescount=0;
commentString=" ";
for(int n <- begin){
 	s=top(end);
 	end=delete(end,0); 
 	if(n==0||s+2==size(sourcecode)){
 	if(n==0)
 	commentString = substring(sourcecode,n,s+2);
 	else commentString = substring(sourcecode,n-1,s+1);
 	clinescount=clinescount+1;
 	}
 	else
 	commentString = substring(sourcecode,n-1,s+2);
 	clinescount =clinescount+ size(findAll(commentString,"\n")); 	
 	}
 	return clinescount;
}
/**
	 *  Counts one line type  comments
	 *@return clinescount
	 */	
int countOLineC(str sourcecode){
int clinescount=0;
 	begin=findAll(sourcecode,"//");
 	for(int n <- begin){
 	if(charAt(sourcecode,n-1)==10)
 	clinescount=clinescount+1;
 	}
 	return clinescount;
}

/**
*counts the actual lines of code,using MultilineMistake,
countMLines,countOLineC functions.
@return linesofcode
*/

int countLines(str sourcecode){
sourcecode = replaceAll(sourcecode," ","");
sourcecode = replaceAll(sourcecode,"\t","");
begin=findAll(sourcecode,"/*");
end=findAll(sourcecode,"*/");
end=MultilineMistake(begin,end);
int clinescount=0;
int linescount=0;
clinescount=countMLines( begin,end,sourcecode)+countOLineC(sourcecode);
	emptylines=findAll(sourcecode,"\n\n");
 if(charAt(sourcecode,0)!=10)
	linescount = size(findAll(sourcecode,"\n"))+1;
	else linescount=size(findAll(sourcecode,"\n"));
	linescount=linescount-clinescount-size(emptylines);
 	if(charAt(sourcecode,size(sourcecode)-1)==10)
 	linescount=linescount-1;
 	return linescount;
	}
	
	
alias SLOC = map[loc file, int sloc];
str stringvar = "";
int lines=0;
int temp=0;
int max=0;
loc maxl;
SLOC sloc(loc project) {
  SLOC result = ();
 locSet = files(project);
 for (i <- locSet) {
 if(i.extension == "java"){
 	stringvar = readFile(i);
 	temp=countLines(stringvar);
 	if (temp>max){
 	max=temp;
 	maxl=i;
 	}
 	lines = lines + temp;
 		}
 }println(lines);
 result = (maxl:max); 
  return result;
}             
     

