/*simple inode link count test for a regular file*/
c_decl{char * lnk; char * rmlnk;}
c_track "lnk" "13"

init{
	int i;
	c_code{lnk = (char *)malloc(13);strcpy(lnk,"ln tc.1 tc.x");
		rmlnk = (char *)malloc(15);strcpy(rmlnk,"rm -f tc.x");};
	
	int count = 0;
	int status = 0;
	c_code {printf("C code executed\n");
		system("rm tc.*; touch tc.1");
		
	};
	i = 2;
	do
	::(i<10)->
		count = 0;
		c_code{lnk[11]=Pinit->i + '0'; printf("%s\n",lnk);system(lnk);
		FILE * fp = popen("../xfstests-dev/src/lstat64 tc.1 | sed -n -e '/ Links: /s/.*Links: *//p' ","r");
		char c;
		while (c = fgetc(fp)) {
			if( c< '0' || c >'9')break;
    			Pinit->count=Pinit->count*10 + (c-'0');
//			printf("Count = %d \n",Pinit->count);
  		}		
		printf("Count = %d \n",Pinit->count);
		};
		printf("Increase i, count = %d %d\n",i,count);
		if
		:: (count != i) -> printf("Not equal %d != %d\n",i,count);status=1;
		:: (count == i) -> skip;
		fi
		i = i+1;
	::(i>=10)-> break;
	od
 	
	i=9;	
	do
	::(i>1)->
		count = 0;
		c_code{FILE * fp = popen("../xfstests-dev/src/lstat64 tc.1 | sed -n -e '/ Links: /s/.*Links: *//p' ","r");
		char c;
		while (c = fgetc(fp)) {
			if( c< '0' || c >'9')break;
    			Pinit->count=Pinit->count*10 + (c-'0');
//			printf("Count = %d \n",Pinit->count);
  		}		
		printf("Count = %d \n",Pinit->count);
		};
		printf("Decrease i, count = %d %d\n",i,count);
		if
		:: (count != i) -> printf("Not equal %d != %d\n",i,count);status=1;
		:: (count == i) -> skip;
		fi
		
		c_code{rmlnk[9]=Pinit->i + '0'; printf("%s\n",rmlnk);system(rmlnk);};
		i = i-1;
	::(i<=1)-> break;
	od
}
