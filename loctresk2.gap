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
    for i in [1..Length(l)] do
        if not (l[i] in l1) and not (l[i]^-1 in l1) then 
            Add(l1,l[i]);
        fi;  
    od;
    return l1;
end; 


# a,b,c se suponen de orden 3
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

        l := [a,a^-1,b,b^-1,a^-1*b,b^-1*a];
        if Length(Set(l)) <> 6 then
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

ExaminaGrupoCondicionUno := function (g,CUELLO)  # Recibe un grupo
    local i,c,c1,l,l1,t,tbuena,seis,aut,orbs,reps,OrdendeG,GrupoGenerado,Orden,g1;
    g1:=Filtered(Elements(g), x-> not x in Centre(g));
    l := Filtered(Elements(g1),x->Order(x)=3);
    l1:=EliminaInversos(l);
    c1 := Combinations(l1,3);
    OrdendeG:=Order(g);
    c:=[];

    for i in [1..Length(c1)] do 
        GrupoGenerado:=Group(c1[i]);    
        Orden:=Order(GrupoGenerado); 
        if Orden = OrdendeG then   
            Add(c,c1[i]);
        fi;
    od;

    # Print("l = ",Length(l),"l1 = ",Length(l1), " \n");
    #   Print("Hay ",Length(c)," combinaciones de tres.\n");
    aut := AutomorphismGroup(g);
    # Print("Ya  calcule los automorfismos \n");
    orbs := Orbits(aut,c,OnSets);
    # Print("Ya  calcule las orbitas \n");
    reps := List(orbs,x->x[1]);    
    tbuena :=[];
    # Print("Hay ",Length(reps)," orbitas de combinaciones de tres.\n");




    for i in [1..Length(reps)] do
        t := reps[i];
        #    PrintTo("/dev/tty","Voy en la combinacion = ",i,"     \r");
        seis := ConjuntoTPrimero(t[1],t[2],t[3]);
        if seis <> fail then
            Add(tbuena,seis);
        fi;
    od;
    # PrintTo("/dev/tty","\n");

    #Print("Voy a quitar repeticiones.\n");
    tbuena := Set(tbuena,Set);
    #Print("Voy a calcular orbitas.\n");
    orbs := Orbits(aut,tbuena,OnSets);
    reps := List(orbs,x->x[1]);


    return List(reps,x->CayleyGraph(g,x));
end;



# Para examinar la condicion dos

ExaminaGrupoCondicionDos := function (g,CUELLO)
    local i,c,c1,l,t,tbuena,seis,aut,orbs,reps,Orden,GrupoGenerado,OrdendeG,CUEllo,aux,g1;
    CUEllo:=CUELLO/2-1;   
    g1:=Filtered(Elements(g), x-> not x in Centre(g));
    
    l := Filtered (Elements(g1),x-> Order(x)>CUEllo);
    c1 := Combinations(l,2);
    OrdendeG:=Order(g);
    c:=[];

    for i in [1..Length(c1)] do 
     
        #    aux:=List(c1[i]);      ......../////////////......................//////////////////////////....................////////////
        if not c1[i][1] in Centralizer(g,c1[i][2]) then 
        GrupoGenerado:=Group(c1[i]);    
        Orden:=Order(GrupoGenerado); 
        if Orden = OrdendeG then  
#            Print("///////////////////Prueba c[i][j] ", c1[i][1], " y ", c1[i][2]);
            Add(c,c1[i]);
        fi;
        fi; 
    od;

    #Print("Hay ",Length(c)," combinaciones de dos.\n");
    aut := AutomorphismGroup(g);
    # Print("Ya  calcule los automorfismos \n");
    orbs := Orbits(aut,c,OnSets);
    #Print("Ya  calcule las orbitas \n");
    reps := List(orbs,x->x[1]);    
    tbuena :=[];
    # Print("Hay ",Length(reps)," orbitas combinaciones de dos.\n");
    for i in [1..Length(reps)] do
        t := reps[i];
        #   PrintTo("/dev/tty","Voy en la combinacion = ",i,"     \r");
        seis := ConjuntoTSegundo(t[1],t[2]);
        if seis <> fail then
            Add(tbuena,seis);
        fi;
    od;
    # PrintTo("/dev/tty","\n");

    #Print("Voy a quitar repeticiones.\n");
    tbuena := Set(tbuena,Set);

    orbs := Orbits(aut,tbuena,OnSets);
    reps := List(orbs,x->x[1]);
    ################################################################################# Print("tbuena=.", orbs,"\n");

    return List(reps,x->CayleyGraph(g,x));
end;



# g es grafica
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

#
ListadeGraficasUno:= function(l,grupo,CUELLO)
    local i,j,t,cuello,b;

    t:= ExaminaGrupoCondicionUno(l,CUELLO);

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
        #  PrintTo("/dev/tty","\n"); 
    else
        cuello:=0;  
    fi; 
    return cuello;
end;




#
ListadeGraficasDos:= function(l,grupo,CUELLO)
    local i,j,t,cuello,b,lg;

    #PrintTo(" ya entre \n");
    t:= ExaminaGrupoCondicionDos(l,CUELLO);
    #PrintTo("  examina grupo condicion dos t", t," \n");


    lg:=[];
    if Length(t) <> 0 then

        for j in [1..Length(t)] do
            b:= GraficaDePuntosYTriangulos(t[j]);
            cuello:= Girth(b);

            #PrintTo(" cuello ", cuello," \n");
            if cuello>(CUELLO-1) then
                Add(lg,b);
                #    return lg;
                PrintTo("/dev/tty","----Cuello de la grafica ",j," =        ",cuello,"      Cond 2,  grupo ", grupo, "\n");    

                PrintTo("/dev/tty","Orden de la grafica  = ", OrderGraph(b),"    \n");
                PrintTo("/dev/tty","es regular =",IsRegularGraph(b),"    El grado de los vertices es =", VertexDegrees(b),"\n"); 

                # PrintTo("/dev/tty","componentes de la bipartita  = ", ConnectedComponents(b),"    \n"); 

                #PrintTo("/dev/tty","vertices de la grafica  = ", VertexNames(b),"    \n");
                #PrintTo("/dev/tty","adyasencia de 1 3k2 = ", Adjacency(t[j], 1),"    \n");
                ;  
                if IsConnectedGraph(b) <> true then
                    PrintTo("/dev/tty","La grafica No es conexa   \n");
                else
                    PrintTo("/dev/tty","La grafica es conexa   \n");  
                fi;        

            fi;
        od;     

        #   PrintTo("/dev/tty","\n"); 

    else
        cuello:=0; 
    fi; 
    return cuello;
end;







#
ParaExaminarGrupos:= function(a,b,CUELLO,gen) # Recibe el intervalo a revisar y el cuello minimo a buscar.
    local i,j,Grupos,CondicionUno, CondicionDos,k,medida,x,y,MedidaDex,NumeroGeneradores,k1,k2;


    for i in [a..b] do
        #PrintTo("/dev/tty","cardinalidad del grupo = ",i,"   \n");
        k:=1;
        Grupos:=AllGroups(i);  #Calcula todos los grupos de orden i.
        medida:=Length(Grupos); 
        x:=[];
        y:=[];
        # PrintTo("/dev/tty"," --medida del grupo ",medida,"------------  \n");

        for j in [1..medida] do 

            # if k=10 then PrintTo("/dev/tty"," ------ Voy en el grupo ",j,"------------  \n"); k:=0 ; fi; k:=k+1; 

            if IsAbelian(Grupos[j])=false then           # Si el grupo es abeliano lo descarta pues el cuello seria ocho. 
                NumeroGeneradores:=Length(GeneratorsOfGroup(Grupos[j]));      

                #                    if  NumeroGeneradores=3 and (i mod 3=0) then 


                # La grafica no es conexa si el numero de generadores es mayor a dos en $Cay(G,T)$ del tipo uno, y mayor a tres en el caso del tipo dos.  
                #                           Add(x,j);
                #                    fi;  

                if  NumeroGeneradores>gen then                
                    Add(y,j);
                fi;  

            fi;
        od;


        PrintTo("/dev/tty","  Orden del grupo", i ,"   \n");
        for k1 in [1..Length(x)] do
            # PrintTo("/dev/tty","   Condicion uno   \n");
            #CondicionUno:=ListadeGraficasUno(Grupos[x[k1]],x[k1],CUELLO);   # Cay(G,T) condicion uno
        od;      


        for k2 in [1..Length(y)] do  
            # PrintTo("/dev/tty","   Condicion dos  \n");
            CondicionDos:=ListadeGraficasDos(Grupos[y[k2]],y[k2],CUELLO);  #Cay(G,T)  condicion dos   
        od;      
    od; 
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
    return;
end;




