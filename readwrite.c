#include <stdio.h>
#include <assert.h>


int first_test ( int a[], int i ) { 
   
   a[i] = 1;

   int temp = a[i];
   
   return temp;
  
}


int second_test (int a[], int i) {  
  int j = 0;
  while (j <= i){
    a[j] = 1;
    j++;
  }
  int temp = a[i];
  return temp;
}

int ten[10] = {1,2,3,4,5,6,7,8,9,0};

int main () {
  printf ("%d \n", first_test(ten, 2));
  printf ("%d \n", second_test(ten,5));
  return 0;
}
