Read("NextClassIntersections.g");

#This file handles the logic behind searching for and filtering feasible class intersections, after being given a modular intersection list.
#For a description of the algorithm, see PAPER.


##############################################################################################################
####INVERSE CLASS COMPRESSION#################################################################################
#Following from the fact that D^(-1) = D, we get |h^G \cap D| = | (h^-1)^G \cap D|. Thus, when we generate a class int,
#this class int must satisfy |h^G \cap D| = | (h^-1)^G \cap D| for all h^G. So, we instead compute our ints by
#combining |(h^G \cup (h^G)^{-1]) \cap D|. If c, c' are the moduli corresponding h^G, (h^G)^{-1}, we set our new modulus
#for |(h^G \cup (h^G)^{-1]) \cap D| to c + c'. In practice, this means we have fewer ints to search through with larger
#moduli, speeding up search times.

#For class representatives h_1, ..., h_n, return lst of pairs [i, j] such that h_i^G = (h_j^G)^{-1}
IndexInverseClassList := function(reps, cls)
	local idx_inv_cls_lst, cl, inv_cl, x, i;

	idx_inv_cls_lst := [];

	for i in [1..Length(cls)] do
		cl := cls[i];

		inv_cl := Filtered(cls, x -> Inverse( reps[i] ) in x)[1];
		
		Append(idx_inv_cls_lst, [ [Position(cls, inv_cl), Position(cls, cl)] ]);
		Sort( Last(idx_inv_cls_lst) );
	od;

	idx_inv_cls_lst := Unique(idx_inv_cls_lst);
	Sort(idx_inv_cls_lst);

	return idx_inv_cls_lst;
end;

#For prelim_cl_ints, ceiling, etc., we build new lsts comb_prelim_cl_ints, comb_ceiling, etc.
#which correspond to the combined ints |(h^G \cup (h^G)^{-1]) \cap D|.
CombineInverseClasses := function(char_table, prelim_cl_ints, ceiling, moduli, char_mat)
	local
	cl, cls, inv_cl,  ord_2_cls_lst, elms_cl, elms_cl_lst, reps,
	idx_inv_cls_lst, 
	comb_prelim_cl_ints, 
	comb_ceiling,
	comb_char_mat,
	comb_moduli,
	x,
	i;

	cls := ConjugacyClasses(char_table);
	reps := List(cls, cl -> Representative(cl));
	ord_2_cls_lst := List(reps, x -> Order(x) = 2);
	idx_inv_cls_lst := IndexInverseClassList(reps, cls);


	comb_prelim_cl_ints := [];
	comb_ceiling := [];
	comb_moduli := [];
	comb_char_mat := [];


	char_mat := TransposedMat(char_mat);
	

	for i in [1..Length(idx_inv_cls_lst)] do
		if idx_inv_cls_lst[i][1] <> idx_inv_cls_lst[i][2] then
			comb_prelim_cl_ints[i] := prelim_cl_ints[idx_inv_cls_lst[i][1]] + prelim_cl_ints[idx_inv_cls_lst[i][1]];
			comb_ceiling[i] := ceiling[idx_inv_cls_lst[i][1]] + ceiling[idx_inv_cls_lst[i][2]];
			comb_moduli[i] := moduli[idx_inv_cls_lst[i][1]] + moduli[idx_inv_cls_lst[i][2]];
			comb_char_mat[i] := (char_mat[idx_inv_cls_lst[i][1]] + char_mat[idx_inv_cls_lst[i][2]])/2; 
		else
			comb_prelim_cl_ints[i] := prelim_cl_ints[idx_inv_cls_lst[i][1]];
			comb_ceiling[i] := ceiling[idx_inv_cls_lst[i][1]];
			comb_moduli[i] := moduli[idx_inv_cls_lst[i][1]];
			comb_char_mat[i] := char_mat[idx_inv_cls_lst[i][1]];
		fi;
	od;

	comb_char_mat := TransposedMat(comb_char_mat);

	return  rec(
		comb_prelim_cl_ints := comb_prelim_cl_ints,
		idx_inv_cls_lst := idx_inv_cls_lst,
		comb_ceiling := comb_ceiling,
		comb_moduli := comb_moduli,
		comb_char_mat := comb_char_mat,
		ord_2_cls_lst := ord_2_cls_lst
		);
end;

#For those classes h^G satisfying h^G = h^{-1}^G but h <> h^{-1}, for which their modulus is odd, we enforce the modulus is even.
#See LEMMA from PAPER
SelfInverseCombModuli := function(comb_prelim_cl_ints, comb_moduli, idx_inv_cls_lst, ord_2_cls_lst, v)
	local i;

	for i in [1..Length(idx_inv_cls_lst)] do
		if (idx_inv_cls_lst[i][1] = idx_inv_cls_lst[i][2]) and (ord_2_cls_lst[i] = false) then
			if comb_prelim_cl_ints[i] mod 2 = 0 and comb_moduli[i] mod 2 = 1 then 
				comb_moduli[i] := 2*comb_moduli[i];
			fi;
		fi;
	od;

	return comb_moduli;
end;

#We uncombine all comb_cl_ints in cl_ints_lst.
UncombineInverseClasses := function(cl_ints_lst, idx_inv_cls_lst)
	local
	cl_ints,
	comb_cl_ints,
	num_cls,
	idx_inv_cls,
	i, j;

	num_cls := Length(Flat(idx_inv_cls_lst));

	for i in [1..Length(cl_ints_lst)] do
		comb_cl_ints := cl_ints_lst[i];
		cl_ints := EmptyPlist(num_cls);

		for j in [1..Length(idx_inv_cls_lst)] do
			idx_inv_cls := idx_inv_cls_lst[j];
			
			if idx_inv_cls[1] <> idx_inv_cls[2] then
				cl_ints[idx_inv_cls[1]] := comb_cl_ints[j]/2;
				cl_ints[idx_inv_cls[2]] := comb_cl_ints[j]/2;
			else
				cl_ints[idx_inv_cls[1]] := comb_cl_ints[j];
			fi;
		od;

		cl_ints_lst[i] := cl_ints;
	od;

	return cl_ints_lst;
end;


##############################################################################################################
####INTERSECTION GENERATION###################################################################################
#This section

#We partn our set of combined classes H_1, ..., H_m into sets A_1, ..., A_n such that all classes inside each A_i have the same modulus.
#The partns {A_i} are represented by the partn_posns lst, in which partn_posns[i] consists of all integers k
#such that H_k \in A_i.
ModuliClassPartition := function(moduli)
	local partn_posns, x;

	partn_posns := [];

	for x in Unique(moduli) do
		Append(partn_posns, [Positions(moduli, x)]);
	od;

	return partn_posns;
end;

#We have partned our combined conjugacy classes into collections A_1, ..., A_n, such that all classes in A_i have the same
#modulus, which we denote as a_i. We now find and return all integer lsts [c_1, ..., c_n] such that c_1 + ... + c_n = stack_size
#and c_i = 0 mod a_i.
PartitionStackSizes := function(partn_posns, moduli, partn_sum_ceiling, stack_size)
	local
	partn_stack_sizes, 
	partn_stack_sizes_lst, 
	zeroes,
	num_moduli,
	next_class_int,
	x;

	num_moduli := Length(partn_posns);
	moduli := Unique(moduli);
	zeroes := ListWithIdenticalEntries(num_moduli, 0);
	next_class_int := "Running";
	partn_stack_sizes_lst := [];

	partn_stack_sizes := PlaceStack(ShallowCopy(zeroes), partn_sum_ceiling, 1, stack_size, stack_size + 1);

	while not next_class_int = "Done" do 
		if partn_stack_sizes mod moduli = zeroes and partn_stack_sizes <= partn_sum_ceiling then 
			Append(partn_stack_sizes_lst, [ShallowCopy(partn_stack_sizes)]);
		fi;

		next_class_int := NextClassIntersection(partn_stack_sizes, partn_sum_ceiling, stack_size, num_moduli-1);
	od;

	return partn_stack_sizes_lst;
end;


#This is a recursive algorithm. We are given a lst [c_1, ..., c_n] of partn_stack_sizes, a lst of partn_posns
#for the partns A_1, ..., A_n of combined classes, the comb_moduli of the combined classes classes, the ceiling of the 
#combined classes, and the number of combined classes, and we initialize a lst partl_cl_ints_lst containing the
#zero lst. Then, here is the pseudocode
#
#   redefine comb_moduli such that comb_moduli[j] equals the modulus of A_j.
#
#   for i in [1.. n]
#	   for partl_comb_cl_ints in partl_comb_cl_ints_lst
#		   over all posns in partn_posns[i] (corresponding to the A_i partn), generate all updtd_partl_comb_cl_ints
#		   satisfying Sum(updtd_partl_comb_cl_ints{partn_posns[i]}) = c_i/comb_moduli[i], and satisfying
#		   updtd_partl_comb_cl_ints[j] = partl_comb_cl_ints[j] whenever j is not in partn_posns[i].
#
#	   Replace partl_comb_cl_ints_lst with the lst of updtd_partl_comb_cl_ints
PartitionClassIntersectionsList := function(partn_posns, partn_stack_sizes, comb_moduli, ceiling, comb_cl_ints_len)
	local
	partl_comb_cl_ints_lst, updtd_partl_comb_cl_ints_lst,
	partl_comb_cl_ints, updtd_partl_comb_cl_ints,
	partn_ceiling, zeroes,
	i;

	comb_moduli := Unique(comb_moduli); 
	zeroes := ListWithIdenticalEntries(comb_cl_ints_len+1, 0); 

	partl_comb_cl_ints_lst := [ShallowCopy(zeroes)]; 

	for i in PositionsProperty(partn_stack_sizes, x -> x <> 0) do 
		updtd_partl_comb_cl_ints_lst := []; 
		partn_stack_sizes[i] := partn_stack_sizes[i]/comb_moduli[i]; 

		for partl_comb_cl_ints in partl_comb_cl_ints_lst do
			partn_ceiling := ShallowCopy(zeroes);
			partn_ceiling{partn_posns[i]} := List(ceiling{partn_posns[i]} / comb_moduli[i], x -> Int(x)); 

			updtd_partl_comb_cl_ints := PlaceStack(ShallowCopy(partl_comb_cl_ints), partn_ceiling, 1, partn_stack_sizes[i], partn_stack_sizes[i] + 1); 
			Append(updtd_partl_comb_cl_ints_lst, [ShallowCopy(updtd_partl_comb_cl_ints)]);

			while not NextClassIntersection(updtd_partl_comb_cl_ints, partn_ceiling, partn_stack_sizes[i], comb_cl_ints_len) = "Done" do 
				Append(updtd_partl_comb_cl_ints_lst, [ShallowCopy(updtd_partl_comb_cl_ints)]);
			od;
		od;

		partl_comb_cl_ints_lst := updtd_partl_comb_cl_ints_lst; 
	od;

	return partl_comb_cl_ints_lst; 
end;

##############################################################################################################
####FILTRATION################################################################################################
#We explain the purpose of FiltrationMatrix. Each comb_cl_ints is generated such that
#	   Sum(comb_cl_ints{partn_posns[i]}) = partn_stack_sizes[i]/comb_moduli[i].
#Therefore, if we define a new vector x such that x{partn_posns[i]} = comb_cl_ints * comb_moduli[i], then
#x + prelim_cl_ints represents a full class int vector, with the inverse classes combined, so we expect
#	   comb_char_mat[i] * x + comb_char_mat[i] * prelim_cl_ints
#to be a sum of eigenvalues, if x + prelim_cl_ints represents a valid class int for the PDS.

#In practice, it is more computationally expensive to first compute x for each comb_cl_ints, and then to check that 
#comb_char_mat[i] * x + comb_char_mat[i] * prelim_cl_ints is a sum of eigenvalues. Instead, we define a new matrix
#filration_mat such that fltr_mat * comb_cl_ints = comb_char_mat * x. Now, we only need to perform one
#multiplication, which is
#	   fltr_mat[i] * comb_cl_ints + comb_char_mat[i] * prelim_cl_ints.

FiltrationMatrix := function(comb_char_mat, comb_moduli, v)
	local fltr_mat, i;

	for i in [1..Length(comb_moduli)] do
		if comb_moduli[i] >= v then
			comb_moduli[i] := 1;
		fi;
	od;

	fltr_mat := TransposedMat(comb_char_mat);
	fltr_mat := List([1..Length(comb_moduli)], i -> comb_moduli[i] * fltr_mat[i]);
	fltr_mat := TransposedMat(fltr_mat);

	return fltr_mat;
end;


#Here, we verify that a given comb_cl_ints is valid. For every combined character degree in comb_char_mat,
#we generate all possible eigenvalue sums.
#Then, for each row i of comb_char_mat and each degree degs[i] in the ith row of comb_char_mat, we compute
#	   eigenvalue_sum - comb_char_mat[i] * prelim_cl_ints
#where eigenvalue_sum is one of the permissible eigenvalue summations generated for the degree degs[i].

#Finally, we check for a given comb_cl_ints that there is some eigenvalue_sum such that
#			   fltr_mat[i] * comb_cl_ints = eigenvalue_sum - comb_char_mat[i] * prelim_cl_ints
#given that fltr_mat[i] * comb_cl_ints + comb_char_mat[i] * prelim_cl_ints must be an eigenvalue sum
#as previously mentioned.
FilterClassIntersections := function(comb_char_mat, fltr_mat, comb_cl_ints_lst, prelim_cl_ints, theta1, theta2)
	local 
	deg, degs,
	eigenvalue_degs_lst,
	mod_output,
	comb_cl_ints,
	output_lst,
	row,
	i,
	x;

	degs := List(comb_char_mat, row -> row[1]);
	eigenvalue_degs_lst := [];

	for deg in Unique(degs) do
		eigenvalue_degs_lst[deg] := List([0..deg], x -> theta1*x + theta2*(deg-x));
	od;

	output_lst := [];

	for i in [1..Length(comb_char_mat)] do
		mod_output := (comb_char_mat*prelim_cl_ints)[i];
		output_lst[i] := List(eigenvalue_degs_lst[degs[i]], x -> x - mod_output);
	od;

	for i in [2..Length(comb_char_mat)] do
		comb_cl_ints_lst := Filtered(comb_cl_ints_lst, comb_cl_ints -> fltr_mat[i]*comb_cl_ints in output_lst[i]);
	od;

	return comb_cl_ints_lst;
end;

#This is dedicated to verifying that [NS] 4.6 (Thesis 6.6) holds.
FilterInverseClasses := function(cl_ints_lst, idx_inv_cls_lst, ord_2_cls_lst)
	local 
	cl_ints,
	fltrd_cl_ints_lst,
	idx_inv_cls,
	keep_int,
	i;

	fltrd_cl_ints_lst := [];

	for cl_ints in cl_ints_lst do
		keep_int := true;

		for i in [2..Length(idx_inv_cls_lst)] do
			idx_inv_cls := idx_inv_cls_lst[i];

			if idx_inv_cls[1] = idx_inv_cls[2] and ord_2_cls_lst[i] = false then
				if cl_ints[idx_inv_cls[1]] mod 2 <> 0 then
					keep_int := false;
				fi;
			fi;
		od;

		if keep_int then
			Append(fltrd_cl_ints_lst, [cl_ints]);
		fi;
	od;

	return fltrd_cl_ints_lst;
end;

CoprimeChars := function(irr, sqrt_delta)
	local lin_char_lst, cp_lin_char_lst;

	lin_char_lst := Filtered( irr, char -> char[1] = 1);
	cp_lin_char_lst := Filtered(lin_char_lst, char -> Gcd(sqrt_delta, Order(char)) = 1);

	return cp_lin_char_lst;
end;

VerifyCosetIntersections := function(cl_ints, group, irr, cls, v, k, sqrt_delta)
	local
	theta_alpha,
	cp_ln_char_lst, char,
	N,
	cosets, coset_size, cl,
	cl_coset_subset_lst, subset_cls,
	i;

	cp_ln_char_lst := CoprimeChars(irr, sqrt_delta);

	if Length(cp_ln_char_lst) = 1 then
		return true;
	fi;
	
	theta_alpha := cl_ints * AsList(cp_ln_char_lst[2]);


	N := Intersection( List(cp_ln_char_lst, char -> KernelOfCharacter(char)));
	cosets := RightCosets(group, N);

	cl_coset_subset_lst := [];

	for i in [1..Length(cosets)] do
		subset_cls := Filtered(cls, cl -> IsSubset(cosets[i], cl));
		cl_coset_subset_lst[i] := List(subset_cls, cl -> Position(cls, cl));
	od;

	coset_size := (k - theta_alpha) * (Size(N)/v);

	if not IsInt(coset_size) then
		return false;
	fi;

	for i in [2..Length(cosets)] do
		if Sum(cl_ints{cl_coset_subset_lst[i]}) > coset_size then
			return false;
		fi;
	od;

	return true;
end;

FilterCosetIntersections := function(cl_ints_lst, group, irr, cls, v, k, sqrt_delta)
	return Filtered(cl_ints_lst, cl_ints -> VerifyCosetIntersections(cl_ints, group, irr, cls, v, k, sqrt_delta));
end;

##############################################################################################################
#####ALL CLASS INTERSECTIONS##################################################################################

AllClassIntersections := function(pds_data, prelim_cl_ints, moduli)
	local
	group, char_table, irr, cls, char_mat, v, k, theta1, theta2,
	stack_size,
	ceiling,
	idx_inv_cls_lst,
	ord_2_cls_lst,
	comb_moduli, comb_char_mat, comb_prelim_cl_ints, comb_ceiling,
	comb_cl_ints_len,
	comb_cl_ints, comb_cl_ints_lst,
	cl_ints_lst,
	partl_comb_cl_ints_lst, #This is an incomplete lst of comb_cl_ints.
	partn_posns,
	fltr_mat,
	partn_ceiling,
	partn_sum_ceiling,
	partn_stacks_sizes, partn_stacks_sizes_lst,
	x, #dummy_variable
	i, j; #iterator

	group := pds_data.group;
	cls := pds_data.cls;
	char_table := pds_data.char_table;
	irr := pds_data.irr;
	char_mat := pds_data.char_mat;
	v := pds_data.v;
	k := pds_data.k;
	theta1 := pds_data.theta1;
	theta2 := pds_data.theta2;

	stack_size := (pds_data.k-Sum(prelim_cl_ints)); 
	ceiling := List(ConjugacyClasses(char_table), Size) - prelim_cl_ints; 

	if Size(Filtered(ceiling, i -> SignInt(i) = -1)) > 0 then 
		return [];
	fi;


	x := CombineInverseClasses(char_table, prelim_cl_ints, ceiling, moduli, char_mat); 
	idx_inv_cls_lst := x.idx_inv_cls_lst;
	comb_prelim_cl_ints := x.comb_prelim_cl_ints;
	comb_char_mat := x.comb_char_mat;
	comb_ceiling := x.comb_ceiling; 
	ord_2_cls_lst := x.ord_2_cls_lst;
	comb_moduli := SelfInverseCombModuli(comb_prelim_cl_ints, x.comb_moduli, idx_inv_cls_lst, ord_2_cls_lst, v);


	partn_posns := ModuliClassPartition(comb_moduli); 
	partn_ceiling := List([1..Length(comb_ceiling)], i -> comb_moduli[i] * Int(comb_ceiling[i]/comb_moduli[i])); 
	partn_sum_ceiling := List(partn_posns, x -> Sum(partn_ceiling{x})); 

	if Sum(partn_sum_ceiling) < stack_size then
		return [];
	fi;


	partn_stacks_sizes_lst := PartitionStackSizes(partn_posns, comb_moduli, partn_sum_ceiling, stack_size); 
	comb_cl_ints_len := Length(comb_moduli)-1; 
	fltr_mat := FiltrationMatrix(comb_char_mat, comb_moduli, v); 
	comb_cl_ints_lst := [];
	
	for partn_stacks_sizes in partn_stacks_sizes_lst do 
		partl_comb_cl_ints_lst := PartitionClassIntersectionsList(partn_posns, partn_stacks_sizes, comb_moduli, comb_ceiling, comb_cl_ints_len);

		partl_comb_cl_ints_lst := FilterClassIntersections(comb_char_mat, fltr_mat, partl_comb_cl_ints_lst, comb_prelim_cl_ints, theta1, theta2);
		Append(comb_cl_ints_lst, partl_comb_cl_ints_lst);
	od;

	for i in [1..Length(comb_cl_ints_lst)] do
		for j in [1..comb_cl_ints_len+1] do
			comb_cl_ints_lst[i][j] := comb_cl_ints_lst[i][j] * comb_moduli[j];
		od;

		comb_cl_ints_lst[i] := comb_cl_ints_lst[i] + comb_prelim_cl_ints;
	od;

	cl_ints_lst := UncombineInverseClasses(comb_cl_ints_lst, idx_inv_cls_lst);
	cl_ints_lst := FilterInverseClasses(cl_ints_lst, idx_inv_cls_lst, ord_2_cls_lst);
	cl_ints_lst := FilterCosetIntersections(cl_ints_lst, group, irr, cls, v, k, theta1-theta2);


	return cl_ints_lst;
end;
