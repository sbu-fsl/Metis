int a=1;
int b=1;
int c=1;
int d=1;
int e=1;
int f=1;
int g=1;
int h=1;

inline assign_flags(a,b,c,d,e,f,g,h) {
    if
        :: a=2;
	:: a=3;
	:: a=4;
	:: a=5;
	:: a=6;
	:: a=7;
	:: a=8;
	:: a=9;
        :: skip;
    fi
    if
        :: b=2;
	:: b=3;
	:: b=4;
	:: b=5;
	:: b=6;
	:: b=7;
	:: b=8;
	:: b=9;
        :: skip;
    fi
    if
        :: c=2;
	:: c=3;
	:: c=4;
	:: c=5;
	:: c=6;
	:: c=7;
	:: c=8;
	:: c=9;
        :: skip;
    fi
    if
        :: d=2;
	:: d=3;
	:: d=4;
	:: d=5;
	:: d=6;
	:: d=7;
	:: d=8;
	:: d=9;
        :: skip;
    fi
    if
        :: e=2;
	:: e=3;
	:: e=4;
	:: e=5;
	:: e=6;
	:: e=7;
	:: e=8;
	:: e=9;
        :: skip;
    fi
    if
        :: f=2;
	:: f=3;
	:: f=4;
	:: f=5;
	:: f=6;
	:: f=7;
	:: f=8;
	:: f=9;
        :: skip;
    fi
    if
        :: g=2;
	:: g=3;
	:: g=4;
	:: g=5;
	:: g=6;
	:: g=7;
	:: g=8;
	:: g=9;
        :: skip;
    fi
    if
        :: h=2;
	:: h=3;
	:: h=4;
	:: h=5;
	:: h=6;
	:: h=7;
	:: h=8;
	:: h=9;
        :: skip;
    fi
}

init{
    do
	:: 
	a=1;
	b=1;
	c=1;
	d=1;
	e=1;
	f=1;
	g=1;
	h=1;
	assign_flags(a,b,c,d,e,f,g,h);
        printf("%d %d\n", a, b);
   od
}
