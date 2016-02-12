LoadPackage("grape");

TrivialAction:= function(x,g) return x; end;

# la siguiente asume que g es vertice transitiva.
EsLocalmente3K2 := function(g) # Verifica que la grafica es localmente 3K2.
    local n;
    n:=InducedSubgraph(g,Adjacency(g,1));
    return OrderGraph(n)=6 and VertexDegrees(n)=[1];
end;



EliminaInversos:=function(l) # Elimina los inversos de una lista dada.
    local l1,i;
    l1:=[];  
    
#    Print("entro a elimina inversos\n");
    
    for i in [1..Length(l)] do
        if not (l[i] in l1) and not (l[i]^-1 in l1) then 
            l1:=Union(l1,[l[i]]);
 #            Print("l1= ",l1,"\n");
        fi;  
    od;
    
    return l1;
end; 

#--------------------------------------------------------=----------------------

CombinacionesDe3:=function(l,g)
    local i,j,kk ,k,aut,Trios,Trios1,Trios11,orbs,Aux,med,set;
    Trios1:=[];
    Trios11:=[];
    
 #      Print("entre a comb de 3 \n");
 aut := AutomorphismGroup(g);

    med:=Length(l);
#    Print("Cantidad de elementos de orden 3 =   ",med," \n");

   
    for i in [1..(med-2)] do
        Trios:=[];

        for j in [(i+1)..(med-1)] do
            if not l[i]*l[j]=l[j]*l[i] then 
                k:=j+1;
                Aux:=[];

                while k<=med do
                    if not l[i]*l[k]=l[k]*l[i] and not l[j]*l[k]=l[k]*l[j] then 
                        set:=Set([l[k]]);
                        Aux:=Union(Aux,[set]);
                        #     Print("    en el while despues de union\n"); 
                    fi;
                    
                        k:=k+1;
                od;
                Aux:=Set(Aux);

                #                Print("\n (Aux)",(Aux)," \n");
                orbs := Orbits(aut,Aux,OnSets);
                #     Print("Ya  calcule las orbitas \n");
                Aux:= List(orbs,x->x[1]);

                for kk in [1..Length(Aux)] do
                    Trios:=Union(Trios,[Set([l[i],l[j],l[kk]])]);
                od;                
            fi;

        od;
        Trios1:=Union(Trios1,Trios);
       # Print("hay ",Length(Trios)," trios con ",i," y ",j,"\n");
       # Print("hay ",Length(Trios1)," trios1 con ",i," y ",j,"\n");
        Trios:=[];
        if Length(Trios1)>2000 then
   #         Print("antes de orbitas\n");
                  orbs := Orbits(aut,Trios1,OnSets);
  #               Print("Ya  calcule las orbitas \n");
                  Trios1:= List(orbs,x->x[1]);
                  Trios11:=Union(Trios11,Trios1);
                  Trios1:=[];              
                   Print("\n hay ",Length(Trios11)," trios11 con ",i," y ",j,"\n\n");
        fi;
          
    od;
    Trios11:=Union(Trios11,Trios1);
    
    aut:=[];
    Aux:=[];
    set:=[];

    Print("hay ",Length(Trios11)," trios\n");
    #Print("lista de Trios ",(Trios),"\n");

    return Trios11;
end;


#----------------:=----------------------------------------

SubgruposCiclicos:=function(g,cuello)
    local X,i,S;
    S:=AllSubgroups(g);    
    X:=[];   

    X:=Filtered(S,x->IsCyclic(x)=true and ((cuello)/2)<=(Order(x)) );
    g:=[];
    S:=[];
    # PrintTo("/dev/tty","Numero de parejas que se formarian = ", (Order(g)-1)*(Order(g)-2),"   \n");

    return X;

end;

SubgruposCiclicos1:=function(g,cuello)
    local X,i,S;
    S:=AllSubgroups(g);    
    X:=[];   

    X:=Filtered(S,x->IsCyclic(x)=true and (3=Order(x)));
    g:=[];
    S:=[];
    # PrintTo("/dev/tty","Numero de parejas que se formarian = ", (Order(g)-1)*(Order(g)-2),"   \n");

    return X;

end;

Interseccion:=function(X,g)

    local X1,X2,X3,X22,X33,i,j,a,b,b1,b2,cont,c,aux,Sets,aut,orbs,Posiciones,med;
    med:=0;    
    X1:=[];
    X2:=[];
    X3:=[];
    X22:=[];
    X33:=[];
    Posiciones:=[];
    #    a:=((Length(x)-1)*(Length(x)))/2;
    #    PrintTo("/dev/tty","Numero de subgrupos clicos ",Length(X),"   \n");
    aux:=X;

    i:=Length(X);

    if i>1 then
        while i>0 do
            # PrintTo("/dev/tty","entre ",i," veces  \n"); 
            if X[i] in aux then
                aux:=Filtered(aux,x->IsSubgroup(X[i],x)=false);
                #  PrintTo("/dev/tty","los q no son subgrupos ",aux,"  \n"); 
                Sets:=Set(Elements(X[i]));        
                Add(X1,Sets);
            fi;
            i:=i-1;
        od;        
        aux:=[];
        Sets:=[];

        #    PrintTo("/dev/tty","Hay  ",Length(X1)," subgrupos buenos \n");     
        #Print("Estoy lista para hacer set.\n");
        X1:=Set(X1,Set);
        #    Print("antes de aut.\n");

        if Length(X1)>1 then
            X2:= Combinations(X1,2);          
            X1:=[];            
            #     PrintTo("/dev/tty","hay ", Length(X2)," parejas de subgrupos \n");
            #     Print("primer pareja",X2[1][1]," \n");
            med:=Length(X2);            
            if med>1 then    
                j:=1;
                while j<=med do
                    Add( X3,Union(Set(X2[j][1]),Set((X2[j][2]))));
                    j:=j+1;    
                od;
                #    PrintTo("/dev/tty","hay ",Length(X3) ," sets de las parejas \n");        
                aut := AutomorphismGroup(g);
                #    Print("Ya  calcule los automorfismos \n");
                orbs := Orbits(aut,X3,OnSets);
                #    Print("Ya  calcule las orbitas \n");
                X33 := List(orbs,x->x[1]);    
                #    PrintTo("/dev/tty","Hay ", Length(X33)," parejas de subgrupos despues de orbitas\n");
                Posiciones:=List(X33,x-> Position(X3,x));
                X33:=[];
                X3:=[];
                ;  
            fi;

            for i in [1..Length(Posiciones)] do
                Add(X22,X2[Posiciones[i]]);
            od;

        fi;
    fi;
    X2:=[];
    Posiciones:=[];
    aut:=[];
    orbs:=[];
    aux:=[];
    X:=[];


    return X22;   
end;


ParejasDeSubgrupos:=function(X1,orden)
    local i,j,c,G,ord,g1,g2,orden1,aux,list1,list2;
    c:=[];
    orden1:=0;
    ord:=0;

    #    PrintTo("/dev/tty"," antes de filtered  \n");
    list1:=Filtered(Elements(X1[1]),x->Order(x)=Length(X1[1]));
    list2:=Filtered(Elements(X1[2]),x->Order(x)=Length(X1[2]));
    X1:=[];

    g1:=list1[1];  
    g2:=list2[1]; 
    list1:=[];
    list2:=[];

    if g1*g2<>g2*g1 then
        G:=Group(g1,g2);
        aux:=Order(G);           
        if orden = aux then   
            Add(c,[g1,g2]);  
        fi;
    fi;    
    G:=[];
    #     PrintTo("/dev/tty","Cantidad de parejas de subgrupos valida ",Length(c),"  \n");
    return c;

end;


#    a,b,c se suponen de orden 3
ConjuntoTPrimero := function (a,b,c)    # Verifica que los elementos no cumplan las condiciones malas en caso del tipo uno. 
    local l;
    l := [a,a^-1,b,b^-1,c,c^-1];

    if Length(Set(l)) <> 6 then
        return fail;
    elif
      a*b = c^-1 then
        return fail;
    elif
      a*b = c then
        return fail;
    elif
      a*b^-1 = c then
        return fail;
    elif
      a*b^-1 = c^-1 then
        return fail;
    elif
      a*c = b then
        return fail;
    elif
      a*c = b^-1 then
        return fail;
    elif
      a*c^-1 = b then
        return fail;
    elif
      a*c^-1 = b^-1 then
        return fail;
    else
        return l;
    fi;
end;

# a,b se asumen de orden distinto a 3
ConjuntoTSegundo := function (a,b) # Verifica que los elementos no cumplan con las condiciones malas en el caso del tipo dos
    local l;
    if Order(a^-1*b)<>3 then 

        l :=Set([a,a^-1,b,b^-1,a^-1*b,b^-1*a]);
        if Length(l) <> 6 then
            return fail;
        elif
          Order(a^-1*b) = 3 then
            return fail;
        elif
          b = a^3 then
            return fail;
        elif
          b^-1 = a^2 then
            return fail;
        elif
          b^2 = a^-1 then
            return fail;
        elif
          a*b = b^-1*a then
            return fail;
        elif
          a^2 = b^2 then
            return fail;
        elif
          a*b = b*a then
            return fail;
        elif
          a^-1*b = a*b^-1*a then
            return fail;
        elif
          a*b = b*a^-1 then
            return fail;
        else
            return l;
        fi;
    else
        return fail;

    fi;

end;

#---------------------------------------------------------------------------




OchoCiclosUno:=function (t)     
    local q,w,e,r,a,b,c,l,l1;
    a:=t[1];
    if t[2]<>a*a then
        b:=t[2];
    else
        b:=t[3];
    fi;
    l:=[a,a^-1,b,b^-1];
    l1:=Filtered(t,x-> not x in l);
    c:=l1[1];
    q:=a*b;
    w:=a*b^-1;
    e:=a*c;
    r:=a*c^-1; 
    if 
      q=b*a or q=b*a^-1 or q=b*c or q=b*c^-1 or q= c*a or q=c*a^-1
      or q=(c^-1)*a or q= (c^-1)*(a^-1) or q=(b^-1)*a or q=(b^-1)*(a^-1)
      or q=(b^-1)*c or q=(b^-1)*(b^-1) then
        return fail;
    elif
      w = b*a^-1 or w=b*c or w=b*c^-1 or w=(b^-1)*c or w=(b^-1)*(c^-1) 
      or w=c*a^-1 or w=(c^-1)*(a^-1) then
        return fail;
    elif
      e =b*a or e=(b^-1)*a or e= c*a or  e=(c)*a^-1 or e=c*b or e=c*b^-1 
      or e= (c^-1)*(a)  or e= (c^-1)*(a^-1)  or e= (c^-1)*(b) or e= (c^-1)*(b^-1) then
        return fail;
    elif
      r = c*a^-1 or r=c*b or r=c*b^-1 or r=(c^-1)*b or r=(c^-1)*(b^-1) then
        return fail;
    else
        return 1;
    fi;
end;


#------------------------------------------------------------------------


Adyacencia:=function(g,cuello)

    local list,i,j,c,k,t,ady,ady1,aux,aux1,aux2;
    #     PrintTo("/dev/tty"," ya entre a adyacencia\n");

    if cuello>4 then

        c:=0;
        ady:=Adjacency(g,1);
        aux2:=Union(ady,[1]);
        aux1:=ady;
        aux:=Union(ady,[1]);   
        #       Add(aux32,1);
        #       Add(aux,1);
        #     Print("aux2 = = = ",aux2,"\n\n");

        t:=[31,127,511,2047];


        if cuello>=5 and cuello<7 then
            c:=1;       
        elif cuello>=7 and cuello<9 then
            c:=2;
        elif cuello>=9 and cuello<11 then
            c:=3;     
        elif cuello>=11 then
            c:=4; 

        fi;

        k:=1;


        while k<=c do
            #          PrintTo("/dev/tty"," en el while \n");
            for i in [1..Length(aux1)] do
                ady1:=Adjacency(g,aux1[i]);        
                for j in [1..Length(ady1)] do 
                    aux:=Union(aux,[ady1[j]]);
                od;
            od;

            aux:=Set(aux);
            aux1:=Filtered(aux,x->not x in aux2); 
            aux2:=aux;
 #Print("\n    .....",Length(aux2),"<",(t[k]));
               
            if Length(aux2)<(t[k]) then
                
                aux:=[];
                aux1:=[];
                aux2:=[];
                ady1:=[];
                ady:=[];
                g:=[];

                return fail;           
            fi;
            k:=k+1;
            
        od; 

    fi;

    aux:=[];
    aux1:=[];
    aux2:=[];
    ady:=[];

    return g;   
end;




# g esuna grafica

GraficaDePuntosYTriangulos := function(g)
    local triang,verts,ady,act,g2;
    ady := function(u,v)
        if not(IsList(u)) and IsList(v) then
            return u in v;
        else
            return false;
        fi;
    end;
    g2 := NewGroupGraph(Group(()),g);
    triang := Cliques(g2);
    return
      UnderlyingGraph(Graph(
              Group(()),
              Union(triang,Vertices(g)),
              TrivialAction,
              ady,
              true));
end;
#-------------------------------------------------------------------------

EsGraficaDeCayley := function (g)
    local aut,cc,reps,l,esono,i;
    aut := AutGroupGraph(g);
    if IsTransitive(aut,Vertices(g)) and Order(aut)=OrderGraph(g) then
        return true;
    else
        esono := false;
        cc := ConjugacyClassesSubgroups(aut);
        reps := List(cc,x->x[1]);
        l := List([1..Length(reps)],x->[x,Order(reps[x])]);
        l := Filtered(l,x->x[2]=OrderGraph(g));
    fi;
 
     for i in [1..Length(l)] do
        if  IsTransitive(reps[l[i][1]],Vertices(g))=true then
            return true;
        fi; 
    od;
    
    return false;
    
end;




ListadeGraficasUno:= function(l,grupo,CUELLO)
    local i,j,t,cuello,b;

    #    t:= ExaminaGrupoCondicionUno(l,CUELLO);
    if Length(t)<>0 then
        for j in [1..Length(t)] do

            b:= GraficaDePuntosYTriangulos(t[j]);
            #  PrintTo("/dev/tty","Voy en la grafica = ",i,"     \r");
            cuello:= Girth(b);

            if cuello > (CUELLO-1) then

                PrintTo("/dev/tty","-----Cuello de la grafica ",j," =             ",cuello,"      Cond  1,   grupo ",grupo,"   \n");

                PrintTo("/dev/tty","Orden de la grafica  = ", OrderGraph(b),"    \n");

                #PrintTo("/dev/tty","La T buena  = ", t[j] ,"    \n");
            fi;
        od;      
    else
        cuello:=0;  
    fi; 
    return cuello;
end;


ListadeGraficas:= function(t,grupo,CUELLO)
    local i,j,cuello,b,lg,lg1,med;

    lg:=[];
    lg1:=[];
    med:=Length(t);

    if med <> 0 then
        for j in [1..med] do
            if (j mod 3)=0 then
                #PrintTo("/dev/tty","________________ voy en la grafica ", j,"_______________ \n");
            fi;
            b:= GraficaDePuntosYTriangulos(t[j]);
            cuello:= Girth(b);
            PrintTo("/dev/tty","----Cuello de la grafica ",j," =        ",cuello,"\n");    
            if cuello>=(CUELLO) then
                Add(lg,b);
                #                Add(lg1,pareja[j]);                
                #return lg;
                PrintTo("/dev/tty","----Cuello de la grafica ",j," =        ",cuello,"      Condicion 1,  grupo ", grupo, "\n");    
                PrintTo("/dev/tty","Orden de la grafica  = ", OrderGraph(b),"    \n");
                PrintTo("/dev/tty","Es una grafica de Cayley? ",EsGraficaDeCayley(b),"\n    El grado de los vertices es =", VertexDegrees(b),"\n"); 
                #                PrintTo("/dev/tty","La pareja que la genero es= ", pareja[j] ,"    \n"); 
                #PrintTo("/dev/tty","adyasencia de 1 3k2 = ", Adjacency(t[j], 1),"    \n");  
                if IsConnectedGraph(b) <> true then
                    PrintTo("/dev/tty","La grafica No es conexa   \n");
                else
                    PrintTo("/dev/tty","La grafica es conexa \n");  
                fi;        
            fi;
        od;
        #PrintTo("/dev/tty","\n");
    fi; 
    t:=[];
    grupo:=0;
    #   pareja:=[];

    return (lg);
end;








ListadeGraficasDos:= function(t,grupo,CUELLO)
    local i,j,cuello,b,lg,lg1,med;

    lg:=[];
    lg1:=[];
    med:=Length(t);

    if med <> 0 then
        for j in [1..med] do
            if (j mod 3)=0 then
                #PrintTo("/dev/tty","________________ voy en la grafica ", j,"_______________ \n");
            fi;
            b:= GraficaDePuntosYTriangulos(t[j]);
            cuello:= Girth(b);
            PrintTo("/dev/tty","----Cuello de la grafica ",j," =        ",cuello,"\n");    
            if cuello>=(CUELLO) then
                Add(lg,b);
                #                Add(lg1,pareja[j]);                
                #return lg;
                PrintTo("/dev/tty","----Cuello de la grafica ",j," =        ",cuello,"      Condicion 2,  grupo ", grupo, "\n");    
                PrintTo("/dev/tty","Orden de la grafica  = ", OrderGraph(b),"    \n");
                PrintTo("/dev/tty","Es una grafica de Cayley =",IsRegularGraph(b)," \n   El grado de los vertices es =", VertexDegrees(b),"\n"); 
                #                PrintTo("/dev/tty","La pareja que la genero es= ", pareja[j] ,"    \n"); 
                #PrintTo("/dev/tty","adyasencia de 1 3k2 = ", Adjacency(t[j], 1),"    \n");  
                if IsConnectedGraph(b) <> true then
                    PrintTo("/dev/tty","La grafica No es conexa \n");
                else
                    PrintTo("/dev/tty","La grafica es conexa \n");  
                fi;        
            fi;
        od;
        #PrintTo("/dev/tty","\n");
    fi; 
    t:=[];
    grupo:=0;
    #   pareja:=[];

    return (lg);
end;

#--------------------------------------------------------=--------------------------------------:=----------------------------------------



ExaminaGrupoCondicionUno := function (g,grupo,CUELLO)  # Recibe un grupo
    local i,c,c1,l,l1,t,t1,tbuena,seis,aut,orbs,reps,reps1,OrdendeG,GrupoGenerado,Orden,g1,sinc,AUX,numdegraf,Cay;

    aut := AutomorphismGroup(g);
      numdegraf:=[];
    g1:=Filtered(Elements(g), x-> not x in Centre(g) and Order(x)=3);
    #  Print("filtered centre",Length(g1),"\n");

    # l := Filtered(Elements(g1),x->Order(x)=3);
    #  Print("filtered centre",Length(l),"\n");


    l1:=EliminaInversos(g1);

    #    orbs := Orbits(aut,l1,OnSets);
    #       Print("Ya  calcule las orbitas \n");
    #       l1 := List(orbs,x->x[1]);
    #      Print("Hay ",Length(l1)," elementos de orden 3.\n");

    #  Print("despues de elimina inversos",Length(l1),"\n");
    l:=[];
    g1:=[];
    if Length(l1)>2 then
  #  aut := AutomorphismGroup(g);
  
    
    c1:=CombinacionesDe3(l1,g);

    #  c1 := Combinations(l1,3);
    l1:=[];

    #   Print("medida de  c1 = ", Length(c1),"\n");


    if Length(c1)>0 then

        # c1:=Set(c1);
        #  Print("combinaciones de 3  = ", Length(c1),"\n");
        #         Print("combinaciones  = ", (c1),"\n");
        OrdendeG:=Order(g);
        c:=[];

        orbs := Orbits(aut,c1,OnSets);
 #       Print("Ya  calcule las orbitas \n");
        c1 := List(orbs,x->x[1]);
#        Print("Hay ",Length(c1)," combinaciones de tres despues de orbitas antesd de grupogenerado.\n");

        for i in [1..Length(c1)] do 
            GrupoGenerado:=Group(c1[i]);    
            Orden:=Order(GrupoGenerado); 
            if Orden = OrdendeG then   
                c:=Union(c,[c1[i]]);
            fi;
        od;
        c1:=[];

        # Print("l = ",Length(l),"l1 = ",Length(l1), " \n");

#        Print("Hay ",Length(c)," combinaciones de tres que generan al grupo.\n");

        if Length(c)>0 then

          #  Print("Ya  calcule los automorfismos \n");
          #  orbs := Orbits(aut,c,OnSets);
          #  Print("Ya  calcule las orbitas \n");
          #  reps := List(orbs,x->x[1]);    
           tbuena :=[];
            orbs:=[];
            reps:=c;
            c:=[];
            
         #   Print("Hay ",Length(reps)," orbitas de combinaciones de tres.\n");
            # Print(":=",reps,"\n");


            for i in [1..Length(reps)] do

                t := reps[i];
           #     PrintTo("/dev/tty","reps = ",t,"     \r");
                if Length(t)=3 then   
                    seis := ConjuntoTPrimero(t[1],t[2],t[3]);
                    if seis <> fail then
                        tbuena:=Union(tbuena,[seis]);
                    fi;
                fi;

            od;
            # PrintTo("/dev/tty","\n");
            reps:=[];

            #Print("Voy a quitar repeticiones.\n");
            tbuena := Set(tbuena,Set);
            #Print("Voy a calcular orbitas.\n");
            orbs := Orbits(aut,tbuena,OnSets);
            reps := List(orbs,x->x[1]);
            Print("Hay  ", Length(reps[1]) ," trios buenos.\n");
            #reps1:=[];
            orbs:=[];



            Cay:= List(reps,x->CayleyGraph(g,x));
            AUX:=Filtered(Cay,x->Adyacencia(x,CUELLO/2)<>fail);

            Print("Despues de usar adyacencias hay ",Length(AUX)," graficas posibles para verificar el cuello\n");


            numdegraf:=ListadeGraficas(AUX,grupo,CUELLO);
            Cay:=[];


            if Length(numdegraf)>0 then
                Print("Ahy ",Length(numdegraf)," graficas con el cuello que deseas \n");
                Print("La mas chica tiene orden = ", OrderGraph(numdegraf[1]) ,"\n");
            fi;


            #    numdegraf:=[];
            reps1:=[];
            AUX:=[];
            c:=[];
            #    cc:=[];

            #return Length(numdegraf);

            #  Print("Hay  ", Length(reps) ," combinaciones buenas despues de calcular orbitas.\n");
            #   Print("Hay  ", Length(reps1) ," combinaciones buenas sin ciclos de 8.\n");
            #  return List(reps1,x->CayleyGraph(g,x));

        fi;
     fi;
 fi;

    aut:=[];

    return numdegraf;

end;



#=-----------------------------------------------------------------------------------------------------------------------------------------

# Para examinar la condicion dos

ExaminaGrupoCondicionDos := function (g,grupo,CUELLO)
    local ij,j,i,k,c,cc,c1,c1c,c11c,c111c,l,t,tbuena,seis,aut,orbs,reps,Orden,Orden1,Orden2,GrupoGenerado,OrdendeG,CUEllo,aux,Subgrupos,Inter,min,g1,g2,g11,g21,Cay,numdegraf,reps1,medida,AUX,tt,tt1;

    #  Print("_+++++++______++++____NUEVO___ GRUPO___+++++++.\n");
     numdegraf:=[];
    aut := AutomorphismGroup(g); 
    reps1:=[];
    # medida:=0;
    reps:=[];
    AUX:=[];
    cc:=[];
#    c11c:=[];
    

    OrdendeG:=Order(g);
    Subgrupos:=SubgruposCiclicos(g,CUELLO);
    Inter:=Interseccion(Subgrupos,g);
    Subgrupos:=[];
    Print("_+++Cantidad de parejas de subgrupos = ",Length(Inter),"\n");

    for ij in [1..Length(Inter)] do
        min:=ParejasDeSubgrupos(Inter[ij],OrdendeG);
        c:=[];    
        medida:=0;
        g1:=[];
        g2:=[];

        for k in [1..Length(min)] do
            cc:=[];

            g11:=[];
            g21:=[];
            g11:=Elements(Group(min[k][1]));
            g21:=Elements(Group(min[k][2]));
            #           Print(" orden de los subgrupos en parejas  ",Length(g11)," y  ",Length(g21),"\n");     
            if CUELLO>=8 then
                g1:=[];
                g2:=[]; 
                g1:=Filtered(g11,x->Order(x)>=CUELLO/2);
                g2:=Filtered(g21,x->Order(x)>=CUELLO/2);
            else
                g1:=[];
                g2:=[]; 
                g1:=Filtered(g11,x->Order(x)>3);
                g2:=Filtered(g21,x->Order(x)>3);
            fi;
            Print("+ Orden de los subgrupos en parejas  ",Length(g1)," y  ",Length(g2),"\n"); 

            c1c:=[];
            c11c:=[];
            c111c:=[];
            
            for tt in [1..Length(g1)] do
                                    
               # Print("voy en el numero ",tt," del subgupo\n"); 
                if not g1[tt] in g2 then
                    #Print("primer if ....");
                               
                    for tt1 in [1..Length(g2)] do
                        #Print("segundo for..");
                                
                        if not g2[tt1] in g1 then
                            # Print("....Segundo if\n");
                            c1:=[];
                            c1:=Set([g1[tt],g2[tt1]]);
                            # Print(".c1...",c1,"\n");
                                     
                            c1c:=Union(c1c,[c1]);
                                      
                            #  Print("..c1c..",c1c,"\n");
                        fi;
                    od;
                fi;
                c11c:=Union(c11c,c1c);
                c1c:=[];
                
                if tt mod 50=0 then
                    c111c:=Union(c111c,c11c);
                    c11c:=[];
                    
                fi;
                
            od;
              c111c:=Union(c111c,c11c);
              c1c:=[];
        
              c1c:=c111c;
              c111c:=[];
            
            c1:=[];

            #Print("hay--",Length(c1c),"- parejas\n");

            if Length(c1c)>0 then    
               # Print("------------------------",c1c,"-\n");
                c1c:=Set(c1c);
               # Print("despues de set\n");
                
                orbs := Orbits(aut,c1c,OnSets);
               #  Print("Ya  calcule las orbitas \n");
                # c1c:=[];            
                c1c:= List(orbs,x->x[1]);    
                orbs:=[];            
                tbuena :=[];
                medida:=Length(c1c);
                #Print("Hay ... ", medida,"...parejas despues de orbitas\n");
            fi;          

            #            Print("c1c-despues de orbitas = ",c1c,"\n");

            # Print(" orden de los subgrupos en parejas ",Length(g1)," y  ",Length(g2)," despues de filtered\n");
            c:=[];

            for tt in [1..Length(c1c)] do
                # c:=[];               
                #             if  i mod 1=0 then     Print("voy en el numero ",i," del subgupo\n"); fi;
                #             if not g1[i] in g2 then
                #                  for j in [1..Length(g2)] do                            
                #                       if not g2[j] in g1 then
                c1:=[];
                #                            c1:=Set([g1[i],g2[j]]);

                c1:=Set([c1c[tt][1],c1c[tt][2]]);
                #               Print("c1 = ",c1,"\n");

                if Length(c1)=2 then


                    if Order(c1[1]^(-1)*c1[2])>=CUELLO/2 then
                        if c1[1]*c1[2]<>c1[2]*c1[1] then
                            if Order(Group(c1))=OrdendeG then
                                seis:=[];                                                
                                seis:=ConjuntoTSegundo(c1[1],c1[2]);
                                if seis <> fail then
                                    #                        Cay:=[];
                                    #                       Cay:= CayleyGraph(g,seis);
                                    #                      AUX:=[[]];
                                    #                    AUX:=Adyacencia(Cay,CUELLO/2);
                                    #      Print("en donde esel problema\n");
                                    #                   if AUX<> fail then
                                    #                  numdegraf:=ListadeGraficasDos([AUX],grupo,CUELLO); 
                                    c:=Union(c,[seis]);
                                    #        Print("c= ",c,"\n");

                                    #             fi;
                                fi;                            
                            fi;                         
                        fi;
                        #    fi;                                    
                    fi;               
                fi;                               
            od;
            cc:=Union(cc,Set(c));
            c:=[];                                  
            # fi;
            #od;
            c1:=[];
            seis:=[];
            #            c:=Set(c);

            # if k mod 30=0 then

        od;
        g1:=[];
        g2:=[];
        g11:=[];
        g21:=[];

        min:=[];  
        #     c:=Set(c);
#        Print("parejas buenas de la pareja de subgrupos ",ij," = ",Length(cc),".\n");


        #        cc:=Union(cc,Set([c]));
        #        cc:=Set(cc,Set);
        #       Print("parejas buenas de la pareja de subgrupos ",ij," = ",Length(cc),".\n");
    #        Print("------------------------",Length(cc),"-\n");

        medida:=0;

        if Length(cc)>0 then    
                # Print("------------------------",cc,"-\n");

            orbs := Orbits(aut,cc,OnSets);
            # Print("Ya  calcule las orbitas \n");
            cc:=[];            
            reps := List(orbs,x->x[1]);    
            orbs:=[];            
            tbuena :=[];
            medida:=Length(reps);
 # Print("Hay tbuena despues de orbitas = ", medida,"\n");
        fi;          

        for i in [1..medida] do
            reps1:=Union(reps1,[reps[i]]);            
        od;
        reps:=[];
        cc:=[];
   # od;


    cc:=[];

    reps:=[];    
    reps1:=Set(reps1);
    # Print("Hay ",Length(reps1)," parejas buenas antes de orbitas\n");

    orbs := Orbits(aut,reps1,OnSets);

    #aut:=[];    
    reps1 := List(orbs,x->x[1]);   
    Print("Hay * ",Length(reps1)," * tbuenas \n");

    Cay:= List(reps1,x->CayleyGraph(g,x));

    AUX:=Filtered(Cay,x->Adyacencia(x,CUELLO/2)<>fail);

    Print("Despues de usar adyacencias hay ",Length(AUX)," graficas posibles para verificar el cuello\n");

    numdegraf:=ListadeGraficasDos(AUX,grupo,CUELLO);
    Cay:=[];

    if Length(numdegraf)>0 then
        Print("Ahy ",Length(numdegraf)," graficas con el cuello que deseas \n");
        Print("La mas chica tiene orden = ", OrderGraph(numdegraf[1]) ,"\n");
    fi;
    
od;
    #   
    reps1:=[];
    AUX:=[];
    c:=[];
    cc:=[];
    aut:=[]; 
    #return Length(numdegraf);
 
    
    return numdegraf;

end;


# g es grafica


ParaExaminarGrupos:= function(a,b,CUELLO,pp) # Recibe el intervalo a revisar y el cuello minimo a buscar.
    local i,j,Grupos,CondicionUno, CondicionDos,k,kkk,medida,x,y,MedidaDex,NumeroGeneradores,kk,k1,k2,Graficas,Es;
    Graficas:=[];
    kk:=0;

    for i in [a..b] do
        PrintTo("/dev/tty","^^^^^@_@_@     Orden del grupo = ",i,"  _@_@_@^^^^^^^^^\n");

        k:=1;
        medida:=0;    
        medida:=NumberSmallGroups(i);
        x:=[];
        y:=[];

        for j in [pp..medida] do 
            Grupos:=[];
            Grupos:=SmallGroup(i,j); # regresa el grupo que esta en el lugar j de orden i  
            
            
            if CUELLO=8 then
                Es:=false;
            else
                Es:=IsAbelian(Grupos);          
           fi;
                
                    #if k=10 then PrintTo("/dev/tty"," ------ Voy en el grupo ",j,"------------  \n"); k:=0 ; fi; k:=k+1; 
           
            
                
                if Es=false then           # Si el grupo es abeliano lo descarta pues el cuello seria ocho. 
                #               Print("almenos esta entrando x no ser abeliano");

                if (i mod 1)=0 then
                    Print("___________++++___GRUPO___", j,"______ +++++++_______.\n"); 
                fi;
                
                #              Print("\n mod de j= ", i mod 3 ," i = ",i);
                if i mod 3 =0 then
                    Print("\n------Condicion 1--------\n");
                    
                    CondicionUno:=ExaminaGrupoCondicionUno(Grupos,j,CUELLO);
                    Graficas:=Union(Graficas,CondicionUno);
                fi;
                 Print("\n------Condicion 2--------\n");
                CondicionDos:=ExaminaGrupoCondicionDos(Grupos,j,CUELLO);    
                Graficas:=Union(Graficas,CondicionDos);
                #Print("\n al salir de con 2");
                
            fi;

            if j mod 5 =0 then   Print("'\n'''Hay ",(Length(Graficas))," graficas con cuello = ",CUELLO," hasta antes del grupo ",j,"'''\n''\n");
            fi;

            if Length(Graficas)>0 and kk=0 then
                Print("'\n'''Hay ",Length(Graficas)," graficas con el cuello que deseas'''\n''\n");
                Print("La mas chica tiene orden ",2*i," y esta en el gupo ",j,"\n");kk:=1;
                kkk:=j;
            fi;

        od;

        if Length(Graficas)>0 and kk=0 then
            Print("'\n'''Hay ",Length(Graficas)," graficas con el cuello que deseas'''\n''\n");
            Print("La mas chica tiene orden ",2*i," y esta en el gupo ",kkk,"\n");kk:=1;
            kkk:=j;
        fi;  
    od;

    if Length(Graficas)>0 then
        Print("\n'\n'''Hay ",Length(Graficas)," graficas con el cuello que deseas'''\n''\n");
        Print("La mas chica tiene orden ",OrderGraph(Graficas[Length(Graficas)])," y esta en el grupo ",kkk,",\n");
    else
        Print("\n\n NO hay graficas con el cuello que deseas\n\n");
    fi;    

    return ;

end;




CantidaddeGrupos:= function (a,b)
    # Calcula la cantidad de grupos en un intervalo
    local i,j,Grupos,CondicionUno, CondicionDos;
    for i in [a..b] do
        PrintTo("/dev/tty","cardinalidad del grupo = ",i,"   \n");
        Grupos:=AllGroups(i);
        PrintTo("/dev/tty","cantidad de grupos = ",Length(Grupos),"   \n");
    od; 
    return i;
end;





CantidadDeGeneradores:= function (a,b,c)
    # Imprime el grupo y la cardinalidad de este, en caso de que el numero de generadores sea c.
    local i,j,Grupos,NumeroGeneradores,medida,x;

    for i in [a..b] do
        PrintTo("/dev/tty","cardinalidad del grupo = ",i,"   \n");
        Grupos:=AllGroups(i);
        medida:=Length(Grupos);
        x:=[];
        #    if IsAbelian()=false then
        for j in [1..medida] do
            if IsAbelian(Grupos[j])=false then
                NumeroGeneradores:=Length(GeneratorsOfGroup(Grupos[j])); 
                #                if  NumeroGeneradores=c then 
                PrintTo("/dev/tty"," No es abeliano   \n");          
                PrintTo("/dev/tty","Grupos= ", j ,"   \n");
                PrintTo("/dev/tty","--------------------  Numero de generadores = ", NumeroGeneradores,"   \n");
                #                fi;  
            fi;
        od;
    od;
    return 0;
end;



