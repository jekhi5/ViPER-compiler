let
	a = (1,2,3),
	b = (4,5),
	c = (6,),
	d = nil
in
	print(a);
	a[0] := b;
	print(a);
	a[0][1] := nil;
	print(a);
	a[2] := c;
	print(a);
	a[1] := nil;
	a
