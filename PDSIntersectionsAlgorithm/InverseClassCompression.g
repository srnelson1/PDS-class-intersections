
IndexInverseClassList := function(cls)
	local
	idx_inv_cls_lst,
	reps,
	cl, inv_cl,
	x,
	i;
	
	reps := List(cls, x -> Representative(x));
	idx_inv_cls_lst := [];

	for i in [1..Length(cls)] do
		cl := cls[i];

		inv_cl := Filtered(cls, x -> Inverse( reps[i] ) in x)[1];
		
		Add(idx_inv_cls_lst, [Position(cls, inv_cl), Position(cls, cl)]);
		Sort( Last(idx_inv_cls_lst) );
	od;

	idx_inv_cls_lst := Unique(idx_inv_cls_lst);
	Sort(idx_inv_cls_lst);

	return idx_inv_cls_lst;
end;


CombineInverseClasses := function(idx_inv_cls_lst, lst)
	local
	cmb_lst,
	i;

	cmb_lst := EmptyPlist(Length(idx_inv_cls_lst));

	for i in [1.. Length(idx_inv_cls_lst)] do
		if idx_inv_cls_lst[i][1] <> idx_inv_cls_lst[i][2] then
			cmb_lst[i] := lst[idx_inv_cls_lst[i][1]] + lst[idx_inv_cls_lst[i][2]];
		else
			cmb_lst[i] := lst[idx_inv_cls_lst[i][1]];
		fi;
	od;

	return cmb_lst;
end;

CombineCharMat := function(idx_inv_cls_lst, char_mat)
	local
	cmb_char_mat,
	idx_inv_cls,
	i;

	cmb_char_mat := EmptyPlist(Length(idx_inv_cls_lst));

	char_mat := TransposedMat(char_mat);

	for i in [1..Length(idx_inv_cls_lst)] do
		idx_inv_cls := idx_inv_cls_lst[i];

		if idx_inv_cls[1] <> idx_inv_cls[2] then
			cmb_char_mat[i] := (char_mat[idx_inv_cls[1]] + char_mat[idx_inv_cls[2]])/2;
		else
			cmb_char_mat[i] := char_mat[idx_inv_cls[1]];
		fi;
	od;

	return TransposedMat(cmb_char_mat);
end;

BuildCmb := function(pds_data, min)
	local
	idx_inv_cls_lst,
	min_cl_ints,
	ceiling;

	idx_inv_cls_lst := IndexInverseClassList(pds_data.cls);
	min_cl_ints := CombineInverseClasses(idx_inv_cls_lst, min.cl_ints);
	ceiling := CombineInverseClasses(idx_inv_cls_lst, List(pds_data.cls, Size) ) - min_cl_ints;

	return  rec(
			idx_inv_cls_lst  := idx_inv_cls_lst,
			ceiling := ceiling,
			min_cl_ints := min_cl_ints,
			moduli := CombineInverseClasses(idx_inv_cls_lst, min.moduli), 
			char_mat := CombineCharMat(idx_inv_cls_lst, pds_data.char_mat),
			len := Length(idx_inv_cls_lst)
		);
end;

####################################################################################################################

UncombineInverseClasses := function(idx_inv_cls_lst, cl_ints)
	local
	idx_inv_cls,
	unc_cl_ints,
	i;

	unc_cl_ints := EmptyPlist(Length(cl_ints));

	for i in [1..Length(idx_inv_cls_lst)] do
		idx_inv_cls := idx_inv_cls_lst[i];
		
		if idx_inv_cls[1] <> idx_inv_cls[2] then
			unc_cl_ints[idx_inv_cls[1]] := cl_ints[i]/2;
			unc_cl_ints[idx_inv_cls[2]] := cl_ints[i]/2;
		else
			unc_cl_ints[idx_inv_cls[1]] := cl_ints[i];
		fi;
	od;

	return unc_cl_ints;
end;

UncombineClassIntersections := function(cls, cl_ints_lst)
	local
	num_cls,
	idx_inv_cls_lst,
	i;

	idx_inv_cls_lst := IndexInverseClassList(cls);
	num_cls := Length(Flat(idx_inv_cls_lst));

	for i in [1..Length(cl_ints_lst)] do
		cl_ints_lst[i] := UncombineInverseClasses(idx_inv_cls_lst, cl_ints_lst[i]);
	od;

	return cl_ints_lst;
end;

