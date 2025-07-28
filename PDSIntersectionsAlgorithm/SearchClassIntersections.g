Read("NextClassIntersections.g");
Read("FilterClassIntersections.g");
Read("InverseClassCompression.g");

#This file handles the logic behind searching for and filtering feasible class intersections, after being given a modular intersection list.
#For a description of the algorithm, see PAPER.



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
#for the partns A_1, ..., A_n of combined classes, the cmb_moduli of the combined classes classes, the ceiling of the 
#combined classes, and the number of combined classes, and we initialize a lst partl_cl_ints_lst containing the
#zero lst. Then, here is the pseudocode
#
#   redefine cmb_moduli such that cmb_moduli[j] equals the modulus of A_j.
#
#   for i in [1.. n]
#	   for partl_cmb_cl_ints in cmb_cl_ints_sublst
#		   over all posns in partn_posns[i] (corresponding to the A_i partn), generate all updtd_partl_cmb_cl_ints
#		   satisfying Sum(updtd_partl_cmb_cl_ints{partn_posns[i]}) = c_i/cmb_moduli[i], and satisfying
#		   updtd_partl_cmb_cl_ints[j] = partl_cmb_cl_ints[j] whenever j is not in partn_posns[i].
#
#	   Replace cmb_cl_ints_sublst with the lst of updtd_partl_cmb_cl_ints
PartitionClassIntersectionsList := function(partn_posns, partn_stack_sizes, cmb_moduli, ceiling, cmb_cl_ints_len)
	local
	cmb_cl_ints_sublst, updtd_cmb_cl_ints_sublst,
	partl_cmb_cl_ints, updtd_partl_cmb_cl_ints,
	partn_ceiling, zeroes,
	i;

	cmb_moduli := Unique(cmb_moduli); 
	zeroes := ListWithIdenticalEntries(cmb_cl_ints_len+1, 0); 

	cmb_cl_ints_sublst := [ShallowCopy(zeroes)]; 

	for i in PositionsProperty(partn_stack_sizes, x -> x <> 0) do 
		updtd_cmb_cl_ints_sublst := []; 
		partn_stack_sizes[i] := partn_stack_sizes[i]/cmb_moduli[i]; 

		for partl_cmb_cl_ints in cmb_cl_ints_sublst do
			partn_ceiling := ShallowCopy(zeroes);
			partn_ceiling{partn_posns[i]} := List(ceiling{partn_posns[i]} / cmb_moduli[i], x -> Int(x)); 

			updtd_partl_cmb_cl_ints := PlaceStack(ShallowCopy(partl_cmb_cl_ints), partn_ceiling, 1, partn_stack_sizes[i], partn_stack_sizes[i] + 1); 
			Append(updtd_cmb_cl_ints_sublst, [ShallowCopy(updtd_partl_cmb_cl_ints)]);

			while not NextClassIntersection(updtd_partl_cmb_cl_ints, partn_ceiling, partn_stack_sizes[i], cmb_cl_ints_len) = "Done" do 
				Append(updtd_cmb_cl_ints_sublst, [ShallowCopy(updtd_partl_cmb_cl_ints)]);
			od;
		od;

		cmb_cl_ints_sublst := updtd_cmb_cl_ints_sublst; 
	od;

	return cmb_cl_ints_sublst; 
end;

##############################################################################################################
#####ALL CLASS INTERSECTIONS##################################################################################

AllClassIntersections := function(pds_data, prelim_cl_ints, moduli)
	local
	group, char_table, irr, cls, char_mat, v, k, theta1, theta2, reps,
	stack_size,
	ceiling,
	idx_inv_cls_lst,
	ord_2_cls_lst,
	cmb, cmb_moduli, cmb_char_mat, cmb_prelim_cl_ints, cmb_ceiling,
	cmb_cl_ints, cmb_cl_ints_lst, cmb_cl_ints_len, cmb_cl_ints_sublst, #This is an incomplete lst of cmb_cl_ints.
	cl_ints_lst,
	fltr_mat,
	partn_posns, partn_ceiling, partn_sum_ceiling, partn_stacks_sizes, partn_stacks_sizes_lst,
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

	reps := List(cls, cl -> Representative(cl));
	ord_2_cls_lst := List(reps, x -> Order(x) = 2);

	stack_size := (pds_data.k-Sum(prelim_cl_ints)); 
	ceiling := List(ConjugacyClasses(char_table), Size) - prelim_cl_ints; 
	
	cmb := CombineInverseClasses(char_table, prelim_cl_ints, ceiling, moduli, char_mat); 
	idx_inv_cls_lst := cmb.idx_inv_cls_lst;
	cmb_prelim_cl_ints := cmb.prelim_cl_ints;
	cmb_char_mat := cmb.char_mat;
	cmb_ceiling := cmb.ceiling; 
	cmb_moduli := SelfInverseCombModuli(cmb_prelim_cl_ints, cmb.moduli, idx_inv_cls_lst, ord_2_cls_lst, v);
	cmb_cl_ints_len := Length(cmb_moduli)-1; 
	cmb_cl_ints_lst := [];

	partn_posns := ModuliClassPartition(cmb_moduli);
	partn_ceiling := List([1..Length(cmb_ceiling)], i -> cmb_moduli[i] * Int(cmb_ceiling[i]/cmb_moduli[i]));
	partn_sum_ceiling := List(partn_posns, x -> Sum(partn_ceiling{x}));
	partn_stacks_sizes_lst := PartitionStackSizes(partn_posns, cmb_moduli, partn_sum_ceiling, stack_size);

	if (Sum(partn_sum_ceiling) < stack_size) or (Size(Filtered(ceiling, i -> SignInt(i) = -1)) > 0) then
		return [];
	fi;


	fltr_mat := FiltrationMatrix(cmb_char_mat, cmb_moduli, v); 
	
	for partn_stacks_sizes in partn_stacks_sizes_lst do 
		cmb_cl_ints_sublst := PartitionClassIntersectionsList(partn_posns, partn_stacks_sizes, cmb_moduli, cmb_ceiling, cmb_cl_ints_len);

		cmb_cl_ints_sublst := FilterClassIntersections(cmb_char_mat, fltr_mat, cmb_cl_ints_sublst, cmb_prelim_cl_ints, theta1, theta2);
		Append(cmb_cl_ints_lst, cmb_cl_ints_sublst);
	od;

	for i in [1..Length(cmb_cl_ints_lst)] do
		for j in [1..cmb_cl_ints_len+1] do
			cmb_cl_ints_lst[i][j] := cmb_cl_ints_lst[i][j] * cmb_moduli[j];
		od;

		cmb_cl_ints_lst[i] := cmb_cl_ints_lst[i] + cmb_prelim_cl_ints;
	od;

	cl_ints_lst := UncmbineInverseClasses(cmb_cl_ints_lst, idx_inv_cls_lst);
	cl_ints_lst := FilterInverseClasses(cl_ints_lst, idx_inv_cls_lst, ord_2_cls_lst);
	cl_ints_lst := FilterCosetIntersections(cl_ints_lst, group, irr, cls, v, k, theta1-theta2);


	return cl_ints_lst;
end;
