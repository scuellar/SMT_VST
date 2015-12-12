#include <stdio.h>


int* swap(int a[], int i, int j){
  int temp;

  temp = a[i];
  a[i] = a[j];
  a[j] = temp;

  return a;  

}

int a[4] = {1,2,3,4};

int main () {
  int* b = swap(a,1,2);
  return 0;
}
