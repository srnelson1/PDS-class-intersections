
#Testing Swartz-Tauschek modular restrictions.
STRestriction := function(group, v, k, lambda, mu)
	local
	sqrt_delta, theta1, theta2,
	st_test, st_comptest;

	sqrt_delta := RootInt( (lambda - mu)^2 + 4 * (k - mu) );
	theta1 := (lambda - mu + sqrt_delta)/2;
	theta2 := (lambda - mu - sqrt_delta)/2;


	if (mu - theta2*(theta1 + 1)) mod sqrt_delta = 0 then
		st_test := true;
	else
		st_test := false;
	fi;

	if (v - 2*k + lambda - theta2*(theta1 + 1)) mod sqrt_delta = 0 then
		st_comptest := true;
	else
		st_comptest := false;
	fi;		


	if ( not st_test ) and ( not st_comptest ) then
		if Size( Center(group) ) <> 1 then
			return false;
		fi;
	fi;


	return true;
end;

