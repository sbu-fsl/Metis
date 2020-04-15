byte n = 0;
byte f=0;


proctype P(){
byte temp = 0;
int i=0;
do
::i<10;
	temp=n+1;
	n = temp;
	i=i+1
::else -> break
od;
f=1;
}


init{
atomic{
	run P();
	run P();
}

/*wait till no of processes active == 1 (i.e only init) */ 
(_nr_pr==1) ->printf("Value of n is %d\n",n);
/*assert (n>2);*/
}
