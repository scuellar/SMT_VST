/* This is the C code for SWAP */
#include <stdio.h>


void swap(int a[], int i, int j){
  int t1, t2;

  t1 = a[i];
  t2 = a[j];
  a[i] = t2;
  a[j] = t1;
}

void swap(int a[], int i, int j){
  int temp;
  temp = a[i];
  a[i] = a[j];;
  a[j] = temp;
}

int four[4] = {1,2,3,4};

int main () {
  swap(four,1,2);

  return 0;
}

