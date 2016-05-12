#############################################################################
##
##                                                              symchm package
##
##  Copyright 2016,                             Jayant Apte, Drexel University
##
##  The .gd file containing global function declarations and the documentation
##  of the itap package. The documentation is written using the AutoDoc Package.
##
##
#############################################################################
#! @Chapter Introduction
#! symchm is a GAP package that for projeting polyhedra using Convex Hull Method (chm). The 'sym' prefix follows from the fact that symchm also supports specifying a group of
#! symmetries of the projection polyhedron. Currently, the main supported class of symmetries is the permutations of co-ordinate dimensions under which the projection is
#! known to be fixed (stabilized setwise). The algorithm CHM proceeds by solving a series of linear programs (LPs)
#! over the input polytope $P$, recovering a vertex of projection per LP solved. It also maintains an inequality description of
#! an inner bound of projection, associated with the convex hull of the subset of vertices found. This description is updated every time a new vertex is found.
#! symchm exploits symmetry in several different ways viz. by solving roughly the number of LPs equal to the number orbits of the symmetry group on vertices of projection and
#! by using symmetric updates of the inequality description. The aforementioned LPs are solved by an external program
#! Qsopt$\_$ex <Cite Key="qs"/> which is a linear program solver
#! by Applegate,Cook,Dash and Espinoza. symchm uses GAP interface package $\texttt{qsopt}\_\texttt{ex-interface}$  <Cite Key="jayantqsint"/> to talk to
#! Qsopt$\_$ex via standard input-output.
#! @Chapter Installation
#!   @BeginCode pkg
GAPInfo.("RootPaths");
#!   @EndCode
#! Assuming you already have GAP 4.5+ installed, you can follow the steps below to install the package:
#! * To get the newest version of symchm, download the .zip archive from <URL>https://github.com/jayant91089/symchm</URL>
#!   and unpack it using $\texttt{unzip  symchm-x.y.zip}$ in the terminal.
#!   Do this preferably inside the $pkg$ subdirectory
#!   of your GAP 4 installation. It creates a subdirectory called $\texttt{qsopt}\_\texttt{ex-interface}$.
#!   If you do not know the whereabouts of the $pkg$ subdirectory, invoke the following in GAP:
#!   @InsertCode pkg
#!   Look for pkg directory inside any of the paths returned.
#! * Once unpacked in the right directory, one can start using symchm by invoking
#! @BeginCode Read
 LoadPackage( "symchm");
 #! @EndCode
#! @InsertCode Read
#! from within GAP. This will automatically load $\texttt{qsopt}\_\texttt{ex-interface}$, if it is available. If instead, it returns 'fail',
#! make sure $\texttt{qsopt}\_\texttt{ex-interface}$ is installed. See the package manual for $\texttt{qsopt}\_\texttt{ex-interface}$ for
#! details of how to install it.
#! @Chapter Usage
#! @Section Available functions

DeclareGlobalFunction("DDstep");
DeclareGlobalFunction("CHM");
