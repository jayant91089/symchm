################################################################################
##
##                                                 qsopt_ex-interface package
##
##  Copyright 2016,           Jayant Apte, Drexel University
##
##  The .gi file containing implementation part of the qsopt_ex-interface package.
##
################################################################################

##
##Utility functions
if not IsBound(DeepCopy_lol) then
DeepCopy_lol:=function(lol)
  local olol,l;
  olol:=[];
  for l in lol do
  Append(olol,[ShallowCopy(l)]);
  od;
  return olol;
end;
fi;

if not IsBound(RecNamesInt) then
RecNamesInt:=function(r)
  # Returns all values in a record
  local i,intnames;
  intnames:=[];
  for i in RecNames(r) do
   Append(intnames,[Int(i)]);
  od;
  return intnames;
end;
fi;

if not IsBound(skipline) then
skipline:=function(str,i)
local j;
if i>Size(str) or i<0 then
  return -1;
fi;
for j in [i..Size(str)] do
  if str[j]='\n' then
    if j=Size(str) then
      return -1;
    else
      return j+1;
    fi;
  fi;
od;
return -1;
end;
fi;


if not IsBound(set2int) then
set2int:=function(s)
  local i,j;
  i:=0;
  for j in s do
    i:=i+2^(Int(j)-1);
  od;
  return i;
end;
fi;

if not IsBound(GenShannonBounded) then
GenShannonBounded:=function(n)
local rlist,mtx,str,i,j,shineq,nset_i,ineq,pairs,p,Klist,K,nset_ij,greq,neq,A,b,sum2one,s;
shineq:=[];
# first add H(X_i|rest)>=0 type inequalities
for i in [1..n] do
  nset_i:=[1..n];
  SubtractSet(nset_i,[i]);
  ineq:=ZeroMutable([1..2^n]);
  ineq[set2int([1..n])+1]:=1;
  ineq[set2int(nset_i)+1]:=-1;
  Append(shineq,[ineq]);
od;
# second, add I(X_i,X_j|X_K) >=0
pairs:=Combinations([1..n],2);
for p in pairs do
  nset_ij:=[1..n];
  SubtractSet(nset_ij,p);
  Klist:=Combinations(nset_ij);
  for K in Klist do
    ineq:=ZeroMutable([1..2^n]);
    ineq[set2int(Union(K,[p[1]]))+1]:=1;
    ineq[set2int(Union(K,[p[2]]))+1]:=1;
    ineq[set2int(Union(K,p))+1]:=-1;
    if Size(K)>0 then
      ineq[set2int(K)+1]:=-1;
    fi;
    Append(shineq,[ineq]);
  od;
od;
shineq:=-shineq;
sum2one:=ZeroMutable([1..2^n-1]);
for i in [1..2^n-1] do
sum2one[i]:=1;
od;
A:=[];
b:=[];
for s in shineq do
  Append(A,[s{[2..Size(s)]}]);
  Append(b,[0]);
od;
Append(A,[sum2one]);
Append(b,[1]);
return [A,b];
end;
fi;

if not IsBound(GenShannonUnBounded) then
GenShannonUnBounded:=function(n)
local rlist,mtx,str,i,j,shineq,nset_i,ineq,pairs,p,Klist,K,nset_ij,greq,neq,A,b,sum2one,s;
shineq:=[];
# first add H(X_i|rest)>=0 type inequalities
for i in [1..n] do
  nset_i:=[1..n];
  SubtractSet(nset_i,[i]);
  ineq:=ZeroMutable([1..2^n]);
  ineq[set2int([1..n])+1]:=1;
  ineq[set2int(nset_i)+1]:=-1;
  Append(shineq,[ineq]);
od;
# second, add I(X_i,X_j|X_K) >=0
pairs:=Combinations([1..n],2);
for p in pairs do
  nset_ij:=[1..n];
  SubtractSet(nset_ij,p);
  Klist:=Combinations(nset_ij);
  for K in Klist do
    ineq:=ZeroMutable([1..2^n]);
    ineq[set2int(Union(K,[p[1]]))+1]:=1;
    ineq[set2int(Union(K,[p[2]]))+1]:=1;
    ineq[set2int(Union(K,p))+1]:=-1;
    if Size(K)>0 then
      ineq[set2int(K)+1]:=-1;
    fi;
    Append(shineq,[ineq]);
  od;
od;
shineq:=-shineq;
sum2one:=ZeroMutable([1..2^n-1]);
for i in [1..2^n-1] do
sum2one[i]:=1;
od;
A:=[];
b:=[];
for s in shineq do
  Append(A,[s{[2..Size(s)]}]);
  Append(b,[0]);
od;
#Append(A,[sum2one]);
#Append(b,[1]);
return [A,b];
end;
fi;

if not IsBound(DeepSort) then
DeepSort:=function(list,nlevels,l)
  local soretdlist,i;
  # l is current level
  # level:=1: only ``list`` is sorted at top level
  # level:=2: each element of list is also sorted and so on...
  # levels 1 and nlevels won't be sorted
  if nlevels = 1 then
    return list;
  fi;
  if nlevels=l then
    return list;
  else
    soretdlist:=EmptyPlist(Size(list));
    for i in [1..Size(list)] do
      soretdlist[i]:=DeepSort(list[i],nlevels,l+1);
      od;
    return soretdlist;
  fi;
end;
fi;

if not IsBound(nextnum) then
nextnum:=function(str,i)
local foundnum, j,k,isneg;
if i>Size(str) or i<0 then
  return -1;
fi;
foundnum:=false;
isneg:=false;
for j in [i..Size(str)] do
  if not str[j]=' ' then
    if IsDigitChar(str[j]) then
      if j-1>=1 and str[j-1]='-' then
        isneg:=true;
      fi;
      foundnum:=true;
      break;
    fi;
  fi;
od;
if foundnum=false then
 return [false,-1,-1]; # [found?, number, next_i]
fi;
for k in [j+1..Size(str)] do
  if not IsDigitChar(str[k]) then
    break;
  fi;
od;
if isneg=true then
  return [true,Int(str{[j-1..k-1]}),k];
else
  return [true,Int(str{[j..k-1]}),k];
fi;
end;
fi;

if not IsBound(writeinefile) then
writeinefile:=function(fname,lin,mtx)
local ostr,row,i,r;
ostr:="";
if Size(lin)=0 then
  ostr:=Concatenation(ostr,"H-representation\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
else
  ostr:= Concatenation(ostr,"H-representation\n","linearity ",String(Size(lin))," ");
  for r in lin do
      ostr:=Concatenation(ostr,String(r)," ");
  od;
  ostr:=Concatenation(ostr,"\nbegin\n",String(Size(mtx))," ",String(Size(mtx[1])), " rational\n");
fi;
for i in [1..Size(mtx)] do
    row:=mtx[i];
    #ostr:=Concatenation(ostr,"0 ");
    for r in row do
        ostr:=Concatenation(ostr,String(r)," ");
    od;
    ostr:=Concatenation(ostr,"\n");
od;
ostr:=Concatenation(ostr,"end");
PrintTo(fname,ostr);
end;
fi;


# symchm functions
RedundQS:= function(A,b,linrows,qs_exec)
  local rowind,redind,s,i,j,rlist;
  rowind:=rec(); # store current row indices to track deletion of rows
  for i in [1..Size(A)] do
    rowind.(i):=i;
  od;
  redind:=[];
  rlist:=LoadQSLP([],A,b,linrows,qs_exec);
  s:=rlist[1];
  for i in [1..Size(A)] do
    LoadQSLPobj(s,A[i]);
    ChangeQSrhs(s,rowind.(i),b[i]+1);
    SolveQSLP(s,[]);
    rlist:=GetQSLPsol_primal(s);
    ChangeQSrhs(s,rowind.(i),b[i]);
    if not rlist[3]>b[i] then
      Append(redind,[i]);
      DelQSrow(s,rowind.(i));
      for j in [i+1..Size(A)] do
        rowind.(j):=rowind.(j)-1;
      od;
    fi;
  od;
  FlushQSLP(s);
  return redind;
end;

RedCube:=function(n,k)
# redundant cube with bad sum=n inequality in kth position
local A,b,onemap,badA,i;
A:=[];
b:=[];
for i in [1..n] do
  Append(A,[Concatenation(ZeroMutable([1..i-1]),[1],ZeroMutable([i+1..n]))]);
  Append(b,[1]);
od;
for i in [1..n] do
  Append(A,[Concatenation(ZeroMutable([1..i-1]),[-1],ZeroMutable([i+1..n]))]);
  Append(b,[0]);
od;
onemap := function ( x )
      return 1;
  end;
badA := List([1..n ],onemap);
A:=Concatenation(A{[1..k-1]},[badA],A{[k..Size(A)]});
b:=Concatenation(b{[1..k-1]},[n],b{[k..Size(b)]});
return [A,b];
end;

DimDeficientCube:=function()
# return a 4D cube with a hidden equality
local A,b,Ao,bo,i;
A:=[[1,0,0,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]];
Append(A,-A);
b:=[1,1,1,1,0,0,0,0];
Append(A,[[-1,-1,1,0]]);
Append(b,[-2]);
Ao:=[];
bo:=[];
for i in [1..Size(A)] do
  if not i in [3,5,6] then
    Append(Ao,[A[i]]);
    Append(bo,[b[i]]);
  fi;
od;
return [A,b];
end;

qs_exec:="/home/aspitrg3-users/jayant/qsopt_interface/dummy";

IsZeroList:=function(list)
local onemap,ones;
onemap := function ( x ) return 1; end;
ones:= List([1..Size(list)],onemap);
if list*ones=0 then
  return true;
else
return false;
fi;
end;

IsFullDimPolyQS:=function(A,b,qs_exec)
## return val: if 1 then FD, if 0 then empty, if 2 then in-between
local i,obj,rlist,s;
for i in [1..Size(A)] do
  Append(A[i],[1]);
od;
Append(A,[ZeroMutable([1..Size(A[1])])]);
A[Size(A)][Size(A[Size(A)])]:=1;
Append(b,[1]);
obj:=ZeroMutable([1..Size(A[1])]);
obj[Size(obj)]:=1;
rlist:=LoadQSLP(obj,A,b,[],qs_exec);
s:=rlist[1];
SolveQSLP(s,[]);
rlist:=GetQSLPsol_primal(s);
FlushQSLP(s);
if rlist[3]>0 then
  return 1;
elif rlist[1]=0 then
  return 0;
else
  return 2;
fi;
end;

FindDepEq:=function(Ai,bi,linrows)
# Find additional inequalitues in A not in linrows that are equalities
local newlin,linA,i,r1,A,b;
A:=DeepCopy_lol(Ai);
b:=DeepCopy_lol(bi);
if Size(linrows)=0 then
  return [];
fi;
newlin:=[];
linA:=[];
for i in [1..Size(A)] do
  if i in linrows then
    Append(linA,[A[i]]);
  fi;
od;
for i in [1..Size(linrows)] do
  Append(linA[i],[b[linrows[i]]]);
od;
r1:=RankMat(linA);
Append(linA,[ZeroMutable([1..Size(linA[1])])]);
for i in [1..Size(A)] do
  if not i in linrows then
    linA[Size(linA)]:=A[i];
    Append(linA[Size(linA)],[b[i]]);
    if not r1<RankMat(linA) then # dependent eq
      Append(newlin,[i]);
    fi;
  fi;
od;
return newlin;
end;

Ranklinrows:=function(Ai,bi,linrows)
local i,linmat,A,b;
A:=DeepCopy_lol(Ai);
b:=DeepCopy_lol(bi);
if Size(linrows)=0 then
  return 0;
fi;
linmat:=[];
for i in [1..Size(A)] do
  if i in linrows then
    Append(linmat,[A[i]]);
  fi;
od;
for i in [1..Size(linrows)] do
  Append(linmat[i],[-b[linrows[i]]]);
od;
Display(linmat);
return RankMat(linmat);
end;


DimPolyQS:=function(Ai,bi,linrowsi,qs_exec)
local i,obj,rlist,s,rlist_dual,A,b,dim,dual_opt,round,coef_rval,linrows;
A:=DeepCopy_lol(Ai);
b:=DeepCopy_lol(bi);
linrows:=ShallowCopy(linrowsi);
Append(linrows,FindDepEq(A,b,linrows));
linrows:=Unique(linrows);
#Display(linrows);
for i in [1..Size(A)] do
  if i in linrows then
    Append(A[i],[0]);
  else
    Append(A[i],[1]);
  fi;
od;
Append(A,[ZeroMutable([1..Size(A[1])])]);
A[Size(A)][Size(A[Size(A)])]:=1;
Append(b,[1]);
obj:=ZeroMutable([1..Size(A[1])]);
obj[Size(obj)]:=1;
rlist:=LoadQSLP(obj,A,b,[],qs_exec);
s:=rlist[1];
round:=0;
while true do
  round:=round+1;
  SolveQSLP(s,[2]);
  rlist:=GetQSLPsol_primal(s);
  Display(Concatenation("primal round ", String(round)," ",String(rlist)));
  #WriteLine(s,"11");
  if rlist[3]>0 then
    FlushQSLP(s);
    return [Size(Ai[1])-Ranklinrows(Ai,bi,linrows),linrows,rlist[Size(rlist)]];
  elif rlist[3]<0 then
    FlushQSLP(s);
    return [0,linrows];
  fi;
  # deal with the in-between case
  rlist_dual:=GetQSLPsol_dual(s);
  Display(Concatenation("dual round ", String(round)," ",String(rlist_dual)));
  dual_opt:=rlist_dual[Size(rlist_dual)];
  Display(rlist_dual);
  for i in [1..Size(dual_opt)] do
    if dual_opt[i]>0 then # tight inequality
      Append(linrows,[i]);
      linrows:=Unique(linrows);
      coef_rval:=ChangeQScoef(s,i,Size(A[1]),0);
      Display(Concatenation("coef_rval:=",String(coef_rval)));
    fi;
  od;
  Append(linrows,FindDepEq(A,b,linrows));
  linrows:=Unique(linrows);
  for i in linrows do
    ChangeQSsense(s,i,"E");
  od;
  #Display("Moded LP:\n");
  #WriteLine(s,"11");
od;
end;

EmbedPoly:=function(A,b,linrows)
local rlinmat,i,trlinmat,erec,row,eq,evar,embedidx,sub,Ae,be;
  if Size(linrows)=0 then
    return [A,b,rec()];
  fi;
  rlinmat:=[];
  for i in linrows do
    Append(rlinmat,[Reversed(A[i])]);
    Append(rlinmat[Size(rlinmat)],[b[i]]);
  od;
  trlinmat:=TriangulizedMat(rlinmat);
  Display(trlinmat);
  erec:=rec();
  for row in trlinmat do
    i:=Position(row,1);
    if not i=fail then
      evar:=Size(row)-i;
      eq:=-Reversed(row{[1..Size(row)-1]});
      eq[evar]:=0;
      Append(eq,[row[Size(row)]]);
      erec.(evar):=eq;
    else
      break;
    fi;
  od;
  for evar in RecNamesInt(erec) do
    for i in [1..Size(A)] do
      if not i in linrows then
        if not A[i][evar]=0 then
          sub:=erec.(evar);
          sub:=A[i][evar]*sub{[1..Size(sub)-1]};
          b[i]:=b[i]-sub[Size(sub)]*A[i][evar];
          A[i]:=A[i]+sub{[1..Size(sub)-1]};
          A[i][evar]:=0;
        fi;
      fi;
    od;
  od;
  embedidx:=[];
  for i in [1..Size(A[1])] do
    if not i in RecNamesInt(erec) then
      Append(embedidx,[i]);
    fi;
  od;
  Ae:=[];
  be:=[];
  for i in [1..Size(A)] do
    if not i in linrows then
      Append(Ae,[A[i]{embedidx}]);
      Append(be,[b[i]]);
    fi;
  od;
  return [Ae,be,erec];
end;

ReadPoly:=function(fname)
local input,str,k,mtx,vec,j,vecstr,pos,rlist,lin,haslin,A,b,row;
input := InputTextFile(fname);;
str:=ReadAll(input);
CloseStream(input);
k:=1;
lin:=[];
haslin:=false;
while not k=-1 do
  #Display(["linloop ",k]);
  if not k+8>Size(str) then
    if not str{[k..k+8]}="linearity" then
      k:=skipline(str,k);
    else
      haslin:=true;
      break;
    fi;
  else
    break;
  fi;
od;
if haslin=true then
  lin:=[];
  j:=skipline(str,k);
  vecstr:=str{[k+9..j-1]};
  pos:=1;
  while not pos=-1 do
    rlist:=nextnum(vecstr,pos);
    if rlist[1]=false then
      break;
    fi;
    Append(lin,[rlist[2]]);
    pos:=rlist[3];
  od;
fi;
k:=1;
while not k=-1 do
  #Display(["begloop ",k]);
  if not k+4>Size(str) then
    if not str{[k..k+4]}="begin" then
      k:=skipline(str,k);
    else
      break;
    fi;
  else
    return [[],[]]; # no matrix in the file
  fi;
od;
mtx:=[];
k:=skipline(str,k);
k:=skipline(str,k);
if k=-1 then
  return mtx;
fi;
while not str{[k..k+2]}="end" do
#Display(["endloop ",k]);
  vec:=[];
  j:=skipline(str,k);
  vecstr:=str{[k..j-1]};
  pos:=1;
  while not pos=-1 do
    rlist:=nextnum(vecstr,pos);
    if rlist[1]=false then
      break;
    fi;
    Append(vec,[rlist[2]]);
    pos:=rlist[3];
  od;
  Append(mtx,[vec]);
  k:=j;
  if k=-1 then
    return [lin,mtx];
  fi;
od;
A:=[];
b:=[];
for row in mtx do
  Append(A,[-row{[2..Size(row)]}]);
  Append(b,[row[1]]);
od;
return [A,b,lin];
end;
SortedCons:=function(cons)
local scons,c;
  scons:=[];
  for c in cons do
    Append(scons,[SortedList([SortedList(c[1]),SortedList(c[2])])]);
  od;
  return SortedList(scons);
end;
networkdbSize:=function(nsrc,nedge)
local str,sizerec;
str:=Concatenation(String(nsrc),String(nedge));
sizerec:=rec(("12"):=4,("13"):=132,("21"):=1,("22"):=333,("23"):=485890,("31"):=9,("32"):=239178);
if IsBound(sizerec.(str)) then
return sizerec.(str);
else
return -1;
fi;
end;

dbnetwork:=function(nsrc,nedge,i,path)
local istr,s,cons,cu,c,nc,cl,j,fid,ix;
if (nsrc,nedge)=(2,3) or (nsrc,nedge)=(3,2) then
fid:=QuoInt(i,1000);
Display(fid);
s:=InputTextFile(Concatenation(path,"networkdb/networklist",String(nsrc),String(nedge),"_",String(fid+1),".g"));
ix:=RemInt(i,1000);
if ix=0 then
  ix:=1000;
fi;
Display(ix);
istr:=Concatenation("local nL",String(nsrc),String(nedge),"_",String(fid+1),";", ReadAll(s), "return nL",String(nsrc),String(nedge),"_",String(fid+1),"[",String(ix),"];");
istr:= InputTextString( istr);;
else
s:=InputTextFile(Concatenation(path,"networkdb/networklist",String(nsrc),String(nedge),".g"));
istr:=Concatenation("local nL",String(nsrc),String(nedge),";", ReadAll(s), "return nL",String(nsrc),String(nedge),"[",String(i),"];");
istr:= InputTextString( istr);;
fi;
CloseStream(s);
nc:= ReadAsFunction(istr)();
Display(nc{[3,4]});
cons:=[];
for c in nc[3] do
  cu:=ShallowCopy(c[2]);
  Append(cu,[c[1]]);
 Append(cons,[[c[2],cu]]);
od;
for c in nc[4] do
  cu:=ShallowCopy(c[2]);
  Append(cu,[c[1]]);
  Append(cons,[[c[2],cu]]);
od;
return [[SortedCons(cons),nsrc,nsrc+nedge],nc[Size(nc)]];
end;

OnNCinstance:=function(nc,g)
local rnc,c,rc1,rc2;
rnc:=[];
for c in nc do
  rc1 := OnSets(c[1],g);
  rc2 := OnSets(c[2],g);
  Append(rnc,[[rc1,rc2]]);
od;
return SortedCons(rnc);
end;

NetSymGroup:=function(NC)
local N,Nx,c,G1,G;
# clean NC
N:=NC[1];
Nx:=SortedCons(N);
# compute stab
G1:=Stabilizer(SymmetricGroup(NC[3]),Nx,OnNCinstance);
G:=Stabilizer(G1,[1..NC[2]],OnSets);
return G;
end;



NCShannonBounded:=function(ncinstance)
local ShOB,i,linrows,con,conlin,j,conineq;
  ShOB:=GenShannonUnBounded(ncinstance[3]);
  i:=Size(ShOB[1])+1;
  linrows:=[];
  # node constraints
  for con in ncinstance[1] do
    conlin:=ZeroMutable([1..2^ncinstance[3]-1]);
    conlin[set2int(con[1])]:=1;
    conlin[set2int(con[2])]:=-1;
    Append(ShOB[1],[conlin]);
    Append(ShOB[2],[0]);
    Append(linrows,[i]);
    i:=i+1;
  od;
  # source independence
  conlin:= ZeroMutable([1..2^ncinstance[3]-1]);
  for j in [1..ncinstance[2]] do
  conlin[set2int([j])]:=1;
  od;
  conlin[set2int([1..ncinstance[2]])]:=-1;
  Append(ShOB[1],[conlin]);
  Append(ShOB[2],[0]);
  Append(linrows,[i]);
  i:=i+1;
  # source and edge rates
  for j in [1..Size(ShOB[1])] do
  ShOB[1][j]:=Concatenation(ZeroMutable([1..ncinstance[3]]),ShOB[1][j]);
  od;
  for j in [1..ncinstance[2]] do # source rate ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=1;
    conineq[ncinstance[3]+set2int([j])]:=-1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
  od;
  for j in [ncinstance[2]+1..ncinstance[3]] do # edge rate ineq
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1;
    conineq[ncinstance[3]+set2int([j])]:=1;
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
    conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
    conineq[j]:=-1; # non-negative
    Append(ShOB[1],[conineq]);
    Append(ShOB[2],[0]);
  od;
  # sum<=1 for rates
  conineq:=ZeroMutable([1..2^ncinstance[3]-1+ncinstance[3]]);
  for j in [1..ncinstance[3]] do
    conineq[j]:=1;
  od;
  Append(ShOB[1],[conineq]);
  Append(ShOB[2],[1]);
  return [ShOB[1],ShOB[2],linrows];
end;

hyperplane:=function(vlist,k)
# vlist has vertices as rows
local mat,i;
mat:=vlist{[2..Size(vlist)]}{[1..k]};
for i in [1..Size(mat)] do
  mat[i]:=mat[i]-vlist[1]{[1..k]};
od;
mat:=TransposedMat(mat);
return NullspaceRatMat(mat)[1];
end;



InitialHull:=function(A,b,k,qs_exec)
# Ax<=b is inequality description
# k is projection dimension
local rlist,s,vlist,obj,i,hlist,vlistk;
rlist:=LoadQSLP([],A,b,[],qs_exec);
s:=rlist[1];
vlist:=[];
vlistk:=[];
#vtx 1
LoadQSLPobj(s,Concatenation([1],ZeroMutable([1..Size(A)-1])));
SolveQSLP(s,[]);
rlist:=GetQSLPsol_primal(s);
Append(vlist,[Concatenation([1],rlist[5])]);
Append(vlistk,[Concatenation([1],rlist[5]{[1..k]})]);
# vtx 2
LoadQSLPobj(s,Concatenation([-1],ZeroMutable([1..Size(A)-1])));
SolveQSLP(s,[]);
rlist:=GetQSLPsol_primal(s);
Append(vlist,[Concatenation([1],rlist[5])]);
Append(vlistk,[Concatenation([1],rlist[5]{[1..k]})]);
while Size(vlist)<k+1 do
  obj:=hyperplane(vlist{[1..Size(vlist)]}{[2..Size(vlist[1])]},k);
  LoadQSLPobj(s,Concatenation(obj,ZeroMutable([1..Size(A)-Size(obj)])));
  SolveQSLP(s,[]);
  rlist:=GetQSLPsol_primal(s);
  if RankMat(Concatenation(vlistk,[Concatenation([1],rlist[5]{[1..k]})]))=Size(vlistk)+1  then
  Append(vlistk,[Concatenation([1],rlist[5]{[1..k]})]);
  Append(vlist,[Concatenation([1],rlist[5])]);
  fi;
  if not Size(vlist)<k+1 then
  break;
  fi;
  LoadQSLPobj(s,Concatenation(-obj,ZeroMutable([1..Size(A)-Size(obj)])));
  SolveQSLP(s,[]);
  rlist:=GetQSLPsol_primal(s);
  if RankMat(Concatenation(vlistk,[Concatenation([1],rlist[5]{[1..k]})]))=Size(vlistk)+1  then
  Append(vlistk,[Concatenation([1],rlist[5]{[1..k]})]);
  Append(vlist,[Concatenation([1],rlist[5])]);
  fi;
od;
hlist:=Inverse(TransposedMat(vlistk));
return [s,vlistk,hlist];
end;

OnEntropySpace:=function(v,g)
  # v is 2^n-1 dim vector
  # g is member of subgroup of S_n
  local n,vg,A;
  n:= Log2Int(Size(v)+1);
  vg:=EmptyPlist(Size(v));
  for A in IteratorOfCombinations([1..n]) do
    if not Size(A)=0 then
      vg[set2int(OnSets(A,g))]:=v[set2int(A)];
    fi;
  od;
  return vg;
end;

TestScript:=function(nsrc,nedge,i)
local rlist1,rlist2,nc,G,A,b,linrows,rlist3,linrows2,rlist4,Ae,be,erec,redind;
rlist1:=dbnetwork(nsrc,nedge,i,"~/gap_install/gap4r7/pkg/qsopt_ex-interface/");
nc:=rlist1[1];
G:=rlist1[2];
rlist2:=NCShannonBounded(nc);
 A:=rlist2[1];
 b:=rlist2[2];
 linrows:=rlist2[3];
 rlist3:=DimPolyQS(A,b,linrows,qs_exec);
 linrows2:=rlist3[2];
 rlist4:=EmbedPoly(A,b,linrows2);
 Ae:=rlist4[1];
  be:=rlist4[2];
  erec:=rlist4[3];
  redind:=RedundQS(Ae,be,[],qs_exec);
  return [Ae{Difference([1..Size(Ae)],redind)},be{Difference([1..Size(Ae)],redind)},erec];
end;

TestScriptMat:=function(nsrc,nedge,i)
local rlist1,rlist2,nc,G,A,b,linrows,rlist3,linrows2,rlist4,Ae,be,erec,redind,mat,j,bmat;
rlist1:=dbnetwork(2,3,i,"~/gap_install/gap4r7/pkg/qsopt_ex-interface/");
nc:=rlist1[1];
G:=rlist1[2];
rlist2:=NCShannonBounded(nc);
 A:=rlist2[1];
 b:=rlist2[2];
 linrows:=rlist2[3];
 rlist3:=DimPolyQS(A,b,linrows,qs_exec);
 linrows2:=rlist3[2];
 rlist4:=EmbedPoly(A,b,linrows2);
 Ae:=rlist4[1];
  be:=rlist4[2];
  erec:=rlist4[3];
  redind:=RedundQS(Ae,be,[],qs_exec);
  bmat:=be{Difference([1..Size(Ae)],redind)};
  mat:=-Ae{Difference([1..Size(Ae)],redind)};
  for j in  [1..Size(mat)] do
    mat[j]:=Concatenation([bmat[j]],mat[j]);
  od;
  return [mat,erec];
end;

OnRateVecs:=function(r,g)
# r is size n list and g \leq S_n
return PermuteVec(r,g);
end;

vtx2polarineq:=function(v)
  # return a s.t. ax<=0 is associated polar ineq
  return Concatenation([1],v);
end;

ineq2polarray:=function(ineq)
  # convert ineq ax-b<=0 to ray [-b a]
  return Concatenation(ineq[Size(ineq)],ineq{[1..Size(ineq)-1]});
end;

IsTermFacet:=function(s,A,b,k,h,z)
  # test facet hx<=b for being terminal for projection of
  # polytope associated with 's' onto first k co-ordinates
  local rlist;
  LoadQSLPobj(s,Concatenation(h,ZeroMutable([1..Size(A[1])-Size(h)])));
  SolveQSLP(s,[]);
  rlist:=GetQSLPsol_primal(s);
  if rlist[3]<=z then
    return [true,rlist[5]];
  else
    return [false,rlist[5]];
  fi;
end;

Polarize:=function(V,H)
# return DD pair of the polar of the homogenization (Vp,Hp) s.t.
# Vp is list of rays while Hp is list of normal vectors a s.t. ax>=0 is the ineq
# input : V is list of vertices, H is inequalities of the form [h z] for hx\leq z
local Hp,v,Vp,h,Zrec,Zr,i,j;
Hp:=[];
for v in V do
Append(Hp,[Concatenation([1],v)]);
od;
Vp:=[Concatenation([-1],ZeroMutable([1..Size(V[1])]))];
for h in H do
  Append(Vp,[Concatenation([-h[Size(h)]],h{[1..Size(h)-1]})]);
od;
Zrec:=rec();
for i in [1..Size(Vp)] do
    Zr:=[];
    for j in [1..Size(Hp)] do
      if Vp[i]*Hp[j]=0 then
        Append(Zr,[j]);
      fi;
    od;
    Zrec.(i):=Zr;
od;
return [Vp,Hp,Zrec];
end;

InstallGlobalFunction(DDstep,
function(V,H,Zrec,h)
# V is list of rays while H is list of normal vectors a s.t. ax>=0 is the ineq
# h is normal vector of the new homogeneous inequality to be added i.e. hx>=0
local prays,nrays,zrays,score,i,Vnew,j,rnew,HRet,VRet,ZrecRet,k,v;
# score the rays against h
prays:=[];
nrays:=[];
zrays:=[];
for i in [1..Size(V)] do
  score:=h*V[i];
  if score>0 then
    Append(prays,[i]);
  elif score<0 then
    Append(nrays,[i]);
  else
    Append(zrays,[i]);
    Zrec.(i):=Concatenation(Zrec.(i),[Size(H)+1]);
  fi;
od;
Vnew:=[];
# compute new rays
for i in [1..Size(prays)] do
  for j in [1..Size(nrays)] do
  # adjtest (algebraic)
    if not Size(H{Intersection(Zrec.(prays[i]),Zrec.(nrays[j]))}) < Size(H[1])-2 then
      if RankMat(H{Intersection(Zrec.(prays[i]),Zrec.(nrays[j]))}) = Size(H[1])-2 then
        rnew:=(h*V[prays[i]])*V[nrays[j]]-(h*V[nrays[j]])*V[prays[i]];
        Append(Vnew,[rnew]);
      fi;
    fi;
  od;
od;
HRet:=Concatenation(H,[h]);
VRet:=[];
ZrecRet:=rec();
k:=1;
for i in prays do
  Append(VRet,[V[i]]);
  ZrecRet.(k):=Zrec.(i);
  k:=k+1;
od;
for i in zrays do
  Append(VRet,[V[i]]);
  ZrecRet.(k):=Zrec.(i);
  k:=k+1;
od;
for v in Vnew do
  ZrecRet.(k):=[];
  Append(VRet,[v]);
  for i in [1..Size(HRet)] do
    if v*HRet[i]=0 then # tight inequality
      Append(ZrecRet.(k),[i]);
    fi;
  od;
  k:=k+1;
od;
return [VRet,HRet,ZrecRet];
end);

# todo:
# test, use erec, take arbitrary projdim, sym
InstallGlobalFunction(CHM,
function(A,b,linrows,k)
local rlist3,rlist2,rlist1,rlist4,rlist5,rlist6,Vp,Ae,be,erec,redind,bproc,Aproc,s,V,H,row,Hp,Zrec,term_h,allterm,h,Vret,Hret,v,linrows2,tcnt,vp;
rlist3:=DimPolyQS(A,b,linrows,qs_exec);
linrows2:=rlist3[2];
rlist4:=EmbedPoly(A,b,linrows2);
Ae:=rlist4[1];
 be:=rlist4[2];
 erec:=rlist4[3];
 redind:=RedundQS(Ae,be,[],qs_exec);
 bproc:=be{Difference([1..Size(Ae)],redind)};
 Aproc:=Ae{Difference([1..Size(Ae)],redind)};
 rlist1:=InitialHull(Aproc,bproc,k,qs_exec);
 s:=rlist1[1];
 V:=rlist1[2]{[1..Size(rlist1[2])]}{[2..Size(rlist1[2][1])]};
 H:=[];
 for row in rlist1[3] do
  Append(H,[Concatenation(-row{[2..Size(row)]},[row[1]])]);
 od;
 rlist2:=Polarize(V,H);
 Vp:=rlist2[1];
 Hp:=rlist2[2];
 Display(Vp);
 Display(Hp);
 Zrec:=rlist2[3];
 term_h:=[];
 tcnt:=0;
 while true do
  allterm:=true;
  for h in H do # find a non-terminal facet
    if not h in term_h then # test
      rlist5:=IsTermFacet(s,Aproc,bproc,k,h{[1..Size(h)-1]},h[Size(h)]);
      if rlist5[1]=true then
        Append(term_h,[h]);
      else
        tcnt:=tcnt+1;
        Display(Concatenation("Non-term facet no.",String(tcnt),String(rlist5[2]{[1..k]})));
        allterm:=false;
        break;
      fi;
    fi;
  od;
  if allterm=true then
    break;
  fi;
  # add new vtx and update
  rlist6:=DDstep(Vp,Hp,Zrec,-Concatenation([1],rlist5[2]{[1..k]}));
  Vp:=rlist6[1];
  Hp:=rlist6[2];
  Zrec:=rlist6[3];
  H:=[];
  for vp in Vp do
    Append(H,[Concatenation(vp{[2..Size(vp)]},[-vp[1]])]);
  od;
 od;
 Vret:=-Hp{[1..Size(Hp)]}{[2..Size(Hp[1])]};
 Hret:=[];
 for v in Vp do
  if not v=Concatenation([-1],ZeroMutable([1..Size(v)-1])) then
    Append(Hret,[Concatenation(v{[2..Size(v)-1]},[-v[1]])]);
  fi;
 od;
 FlushQSLP(s);
 return [Vret,Hret];
end);
# Symmetry Exploitation Functions
SymmetrizeV:=function(V,G,actfunV)
# obtain new polar  inequalities to insert and symmetrize the initial hull
local Vs,v,g,vg;
Vs:=DeepCopy_lol(V);
for v in V do
  for g in G do
    vg:=actfunV(v,g);
    if not vg in Vs then
      Append(Vs,[vg]);
    fi;
  od;
od;
return List(Vs,vtx2polarineq);
end;


SymInitialHull:=function(A,b,erec,projdim,G,actfunV,actfunH,qs_exec)
local rlist,vlist,hlist,Vs;
  rlist:=InitialHull(A,b,projdim,qs_exec);
  vlist:=rlist[2];
  hlist:=rlist[1];
  Vs:=SymmetrizeV(vlist,G,actfunV);
end;
