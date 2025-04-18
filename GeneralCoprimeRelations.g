
#Testing Swartz-Tauschek modularity restrictions.
TestPDSParam:= function(v,k,lambda,mu)
	local Delta, sqrtDelta, theta1, theta2, gamtest, gamcomptest;

	Delta:= (lambda - mu)^2 + 4*(k - mu);

	if Delta < 0 then
		return "Nonintegral!";
	fi;

	sqrtDelta:= RootInt(Delta,2);

	theta1:= (lambda - mu + sqrtDelta)/2;
	theta2:= (lambda - mu - sqrtDelta)/2;


	if not IsInt(sqrtDelta) then
		return "Nonintegral!";
	elif not IsInt(theta1) then
		return "Nonintegral!";
	elif not IsInt(theta2) then
		return "Nonintegral!";
	fi;
	#Apply the test to the original graph.

	if RemInt(mu - theta2*(theta1 + 1), sqrtDelta) = 0 then
		gamtest:= true;
	else
		gamtest:= false;
	fi;

	#Apply the test to the complement.

	if RemInt(v - 2*k + lambda - theta2*(theta1 + 1), sqrtDelta) = 0 then
		gamcomptest:= true;
	else
		gamcomptest:= false;
	fi;		

	#Return the results. Which graph "failed" the test (and would thus
	#need to have every conjugacy class meet the PDS) is listed in parentheses.

	if gamtest then
		if gamcomptest then
			return "No restrictions";
		else 
			return "Possibly genuinely nonabelian (complement)";
		fi;
	else
		if gamcomptest then
			return "Possibly genuinely nonabelian (original graph)";
		else 
			return "Infeasible if center nontrivial";
		fi;
	fi;				 

end;

#If params are infeasible for groups with nontrivial centers, then remove these groups.
TestPDSParamCenter:= function(groups, v,k,lambda,mu)
	local result, group;

	result := TestPDSParam(v, k, lambda, mu);
	
	if result = "Nonintegral!" then
		return "Nonintegral!";
	elif result = "Infeasible if center nontrivial" then
		groups := Filtered(groups, group -> Size(Center(group)) = 1);
	fi;

	return groups;
end;


#Checks if group is valid for given params using Theorem 3.12
IsValidGroup := function(group, v, k, lambda, mu)
    local sqrt_delta, theta1, theta2,
	pi_1, pi_2,
	size_lin_group,
	cp_lin_gp_primes1, cp_lin_gp_primes2,
	p;

    sqrt_delta := Root((lambda - mu)^2 + 4*(k - mu), 2);
    theta1 := (lambda - mu + sqrt_delta)/2;
    theta2 := (lambda-mu - sqrt_delta)/2;
	size_lin_group := v/Size(DerivedSubgroup(group));

	pi_1 := Product( Filtered(FactorsInt(k-theta1), p -> sqrt_delta mod p <> 0) ); #FactorsInt(n) returns only prime values so long as n < 10^18
	pi_1 := pi_1 / Gcd(mu, pi_1);
	pi_2 := Product( Filtered(FactorsInt(k-theta2), p -> sqrt_delta mod p <> 0) );
	pi_2 := pi_2 / Gcd(mu, pi_2);
	cp_lin_gp_primes1 := PrimeDivisors( Gcd(size_lin_group, pi_1) ); 
	cp_lin_gp_primes2 := PrimeDivisors( Gcd(size_lin_group, pi_2) );

	if Product(cp_lin_gp_primes1) > 1 or Product(cp_lin_gp_primes2) > 1 then #verify linear group has some factor coprime to sqrt_delta
		if Gcd(pi_1, size_lin_group) = 1 or Gcd(pi_2, size_lin_group) = 1 then #By [NS] Corollary 3.9 (Thesis 5.10), one of these should equal 1.
			if IsSolvableGroup(group) then
				if Product(List(cp_lin_gp_primes2, p -> pi_1 mod p)) = 1 or Product(List(cp_lin_gp_primes1, p -> pi_2 mod p)) = 1 then #By [NS] Theorem 3.12 (Thesis 5.13), one of these should equal 1.
					return true;
				else
					return false;
				fi;
			fi;
		fi;
	fi;

    return true;
end;

FindCoprimeGroups := function(v, k, lambda, mu)
	local groups, group, is_valid_group, valid_groups;

	groups := Filtered(AllSmallGroups(v), group -> not IsAbelian(group));
	groups := TestPDSParamCenter(groups, v, k, lambda, mu);
	groups := Filtered(groups, group -> not IsAbelian(group));
	valid_groups := [];

	for group in groups do
		if IsValidGroup(group, v, k, lambda, mu) then
			Append(valid_groups, [group]);
		fi;
	od;

	return valid_groups;
end;