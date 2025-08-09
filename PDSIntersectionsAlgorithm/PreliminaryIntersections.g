#The principle function in this file is PreliminaryIntersections, which returns a vector such that the ith index consists
#of the minimal possible conjugacy class PDS intersection for conjugacy class i.
#Here, we apply in particular [NS] 3.9 (Thesis 5.11) and [NS] 4.1 (Thesis 6.1).

##############################################################################################################
##############################################################################################################
#Let H be the largest subgroup of the linear group of G such that |H| is coprime to sqrt_delta. Set N to be the
#intersection of all kernels of the characters of H. The functions ClassesOutsideN and NonNClIntersections take all
#conjugacy classes not contained by N,and applies NS 3.9 (Thesis 5.11) to compute the conjugacy class
#intersection sizes for those classes.

#This collects all classes which are not contained N, and which consists of elements with order coprime to delta
ClassesOutsideN := function(group, char_mat, cls, sqrt_delta)
	local
	lin_chars, cp_lin_chars, lin_char, order,
	cl, non_N_cls,
	ones,
	index,
	x;

	lin_chars := Filtered(char_mat, x -> x[1] = 1);

	cp_lin_chars := [];
	non_N_cls := [];

	for lin_char in lin_chars do
		order := Maximum( List(lin_char, x -> Conductor(x)) );

		if Gcd(order, sqrt_delta) = 1 then
			Append(cp_lin_chars, [lin_char]);
		fi;
	od;

	ones := ListWithIdenticalEntries(Length(cp_lin_chars), 1);

	for cl in cls do
		index := Position(cls, cl);

		if List(cp_lin_chars, x -> x[index]) <> ones then
			Append(non_N_cls, [cl]);
		fi;
	od;
	
	return non_N_cls;
end;


#We use [NS] 3.9 (Thesis 5.11) to compute the conjugacy class intersection sizes for those classes which are not contained in N.
#and which consist of elements with order coprime to delta.
NonNClIntersections := function(group, char_mat, cls, v, k, theta1, theta2)
	local 
	cl,
	non_N_cls, #cls not contained by N
	centralizer_size,
	theta1_cl_intersection_size, theta2_cl_intersection_size, #equals the cl intersection size depending on choice of theta1, theta2
	non_N_cl_intersection, #records intersection sizes corresponding to theta1, theta2 for a particular cl not in N
	non_N_cl_intersection_lst; #records intersection sizes corresponding to theta1, theta2 for all cl not in N

	non_N_cls := ClassesOutsideN(group, char_mat, cls, theta1-theta2);
	non_N_cl_intersection_lst := [];

	for cl in non_N_cls do
		centralizer_size := v/Size(cl);
		theta1_cl_intersection_size := (k - theta1)/centralizer_size; #see [NS] 3.9 (Thesis 5.11) for this formula.
		theta2_cl_intersection_size := (k - theta2)/centralizer_size;

		non_N_cl_intersection := [];

		if IsInt(theta1_cl_intersection_size) and IsInt(theta2_cl_intersection_size) then
			non_N_cl_intersection[1] := theta1_cl_intersection_size;
			non_N_cl_intersection[2] := theta2_cl_intersection_size;

		elif IsInt(theta1_cl_intersection_size) then
			non_N_cl_intersection[1] := theta1_cl_intersection_size;
			non_N_cl_intersection[2] := -1; #if theta2 has invalid intersection, place -1

		elif IsInt(theta2_cl_intersection_size) then
			non_N_cl_intersection[1] := -1;
			non_N_cl_intersection[2] := theta2_cl_intersection_size; #if theta1 has invalid intersection, place -1

		else
			return fail;
		fi;

		non_N_cl_intersection_lst[Position(cls, cl)] := non_N_cl_intersection;
	od;

	return non_N_cl_intersection_lst;
end;

##############################################################################################################
##############################################################################################################

#for a given prime power q, we apply [NS] 4.1 (Thesis 6.1) to calculate the modular intersection size for each conj class.
ModularIntersections := function(centralizer_sizes,  k, theta2, q)
	local 
	cl_mod_q_ints, #class ints mod q
	i; #iteration

	cl_mod_q_ints := EmptyPlist(Length(centralizer_sizes));

	for i in [1..Length(centralizer_sizes)] do
		if centralizer_sizes[i] mod q <> 0 then #i for which  (k-theta2)/centralizer_sizes[i] is computable mod q (these correspond to p_bound_values)
			cl_mod_q_ints[i] := (k-theta2)/centralizer_sizes[i] mod q; #compute intersection mod q.
		fi;
	od;

	return cl_mod_q_ints;
end;

#We use ModularIntersections to get, for a specific conjugacy class, each intersection size of that conjugacy class mod q.
#We then use the Chinese Remainder Theorem to compute the largest possible minimum intersection size for each conjugacy class.
ModularClassIntersections := function(char_table, v, k, theta1, theta2)
	local 
	num_cls,
	centralizer_sizes,
	primes_delta, prime_powers_delta, #primes and prime powers in the decomposition of delta
	q, #a particular prime power dividing delta
	cl_mod_q_ints, #lst for intersection of each cl with D mod q.
	cl_mod_q_ints_rec, #lst of all cl_mod_q_ints for each q.
	mod_cl_ints, #cl ints such that mod_cl_ints[i] = cl_mod_q_ints[i] mod q for all i and q.
	moduli, #values q used to calculate mod_cl_ints[i] for each i.
	defined_q_values, #indices such that ModularIntersections(centralizer_sizes,  k, theta2, q) is defined (see ModularIntersections)
	defined_cl_q_ints, #lst of ints mod q for a given cl.
	i, j; #iteration variables

	num_cls := Length(ConjugacyClasses(char_table));
	centralizer_sizes := List(ConjugacyClasses(char_table), i -> v/Size(i)); #centralizer sizes of cls
	primes_delta := PrimePowersInt(theta1-theta2);
	prime_powers_delta := List([1.. Length(primes_delta)/2], i -> primes_delta[2*i - 1] ^ primes_delta[2*i]);

	cl_mod_q_ints_rec := rec( 1 := ListWithIdenticalEntries(num_cls, 0));

	for q in prime_powers_delta do #Apply [NS] 4.1 (Thesis 6.1) to get mod q intersection for each conjugacy class
		cl_mod_q_ints_rec.(q) := ModularIntersections(centralizer_sizes, k, theta2, q);
	od;
	Append(prime_powers_delta, [1]);


	mod_cl_ints := EmptyPlist(num_cls); #will contain largest possible minimum intersection size for each conjugacy class using Chinese Remainder Theorem
	moduli := EmptyPlist(num_cls); #contains Chinese Remainder Theorem value for which the ith intersection is valid.

	for i in [2..num_cls] do
		defined_q_values := Filtered(prime_powers_delta, q -> IsBound( cl_mod_q_ints_rec.(q)[i]) ); #values for which centralizer_sizes[i] mod q <> 0
		defined_cl_q_ints := List(defined_q_values, q -> cl_mod_q_ints_rec.(q)[i] ); #cl ints of centralizer_sizes[i] mod q <> 0

		mod_cl_ints[i] := ChineseRem(defined_q_values, defined_cl_q_ints);
		moduli[i] := Product(defined_q_values);
	od;

	mod_cl_ints[1] := (k - theta2 + v*theta2) mod ((theta1-theta2)/Gcd(v, theta1-theta2)); #See [NS] 4.1 (Thesis 6.1) for the origin of this equality.
	moduli[1] := k;

	return rec( mod_cl_ints := mod_cl_ints, moduli := moduli);
end;


##############################################################################################################
####FILTRATION################################################################################################


IsValidPreliminaryIntersection := function(char_mat, min_cl_ints, k, cp_delta)
	local  phi_1, sum_min_cl_ints;

	phi_1 := char_mat*min_cl_ints * List(char_mat, row -> row[1]); #This corresponds to calculating Phi(1).

	sum_min_cl_ints := Sum(min_cl_ints);

	if sum_min_cl_ints > k then
		return false;

	elif (sum_min_cl_ints - k) mod cp_delta <> 0 then
		return false;

	elif phi_1 mod cp_delta <> 0 then
		return false;
	fi;

	return true;
end;


##############################################################################################################
##############################################################################################################

#This function calls ModularClassIntersections and NonNClIntersections to generate two distinct intersection
#lsts using [NS] 4.1 (Thesis 6.1) and [NS] 3.8 (Thesis 5.11). It then combines these lasts into one, preliminary intersection called prelim_ints
#such that all values in prelim_ints satisfy [NS] 4.1 (Thesis 6.1) and [NS] 3.8 (Thesis 5.11).
#This function also returns a secondary lst, moduli, consisting of the largest modulus x such that if c is the size of the
#intersection of the ith conjugacy class with a possible PDS, then prelim_ints[i] = c mod x.
MinimalIntersections := function(pds_data)
	local
	group, char_table, char_mat, cls, v, k, theta1, theta2,
	moduli, mod_cl_ints,
	nonN_cl_intersection_lst, #lst of all ints for non N conjugacy class with elements of order coprime to delta.
	theta1_cl_intersection, theta2_cl_intersection, #class ints of non N conjugacy classes for theta1, theta2.
	min_cl_ints, min_cl_ints_lst, #lst of class ints
	dummy_lst, x, #dummy variables
	i;

	group := pds_data.group;
	char_table := pds_data.char_table;
	char_mat := pds_data.char_mat;
	cls := pds_data.cls;
	v := pds_data.v;
	k := pds_data.k;
	theta1 := pds_data.theta1;
	theta2 := pds_data.theta2;

	x := ModularClassIntersections(char_table, v, k, theta1, theta2);
	mod_cl_ints := x.mod_cl_ints;
	moduli := x.moduli;

	nonN_cl_intersection_lst := NonNClIntersections(group, char_mat, cls, v, k, theta1, theta2);

	if nonN_cl_intersection_lst = fail then #If non N ints do not exist, we communicate that it failed.
		return rec(min_cl_ints_lst := mod_cl_ints, 
				   moduli := moduli,
				   successful := false,
				   fail_reason := "NonNClIntersections Failed"
				   );
	fi;

   min_cl_ints_lst := [[]];

	for i in [1..Length(ConjugacyClasses(char_table))] do
		if IsBound(nonN_cl_intersection_lst[i]) then #if nonN intersection is defined for index i
			theta1_cl_intersection := nonN_cl_intersection_lst[i][1]; #then grab theta1, theta2 ints
			theta2_cl_intersection := nonN_cl_intersection_lst[i][2];

			if theta1_cl_intersection <> -1 and theta2_cl_intersection <> -1 then #Finally, add to all lsts the theta1, theta2 ints (if they exist)
				dummy_lst := List(min_cl_ints_lst, x -> Concatenation(x, [theta1_cl_intersection]));
				min_cl_ints_lst := List(min_cl_ints_lst, x -> Concatenation(x, [theta2_cl_intersection]));

				min_cl_ints_lst := Concatenation(min_cl_ints_lst, dummy_lst);
				
			elif theta1_cl_intersection <> -1 then
				min_cl_ints_lst := List(min_cl_ints_lst, x -> Concatenation(x, [theta1_cl_intersection]));

			else
				min_cl_ints_lst := List(min_cl_ints_lst, x -> Concatenation(x, [theta2_cl_intersection]));

			fi;

			moduli[i] := k;
		else
			min_cl_ints_lst := List(min_cl_ints_lst, x -> Concatenation(x, [mod_cl_ints[i]]) ); #otherwise, set intersection to modular value
		fi;
	od;
	
	for min_cl_ints in min_cl_ints_lst do #Remove invalid min_cl_ints
		if not IsValidPreliminaryIntersection(char_mat, min_cl_ints, k, (theta1-theta2)/Gcd(v, theta1-theta2)) then
			return rec(min_cl_ints_lst := min_cl_ints_lst, 
					   moduli := moduli,
					   successful := false,
					   fail_reason := "IsValidPreliminaryIntersection Failed" #if everything fails, return unsuccessful
					   );
		fi;
	od;

	return rec(min_cl_ints_lst := min_cl_ints_lst,
			   moduli := moduli,
			   successful := true,
			   fail_reason := "None"
			   );
end;
