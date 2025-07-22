#include <stddef.h>
#include <limits.h>

/*@ predicate sorted(int* arr, integer end) =
      \forall integer i, j ; 0 <= i <= j < end ==> arr[i] <= arr[j] ;
    predicate element_level_sorted(int* array, integer end) =
      \forall integer i ; 0 <= i < end-1 ==> array[i] <= array[i+1] ; 
*/

/*@ requires \valid_read(arr + (0 .. len-1));
    requires sorted(arr, len) ;
*/
size_t bsearch(int* arr, size_t len, int value);

/*@
  requires element_level_sorted(arr, len) ;
  assigns  \nothing ;
  ensures  sorted(arr, len);
*/
void element_level_sorted_implies_sorted(int* arr, size_t len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant sorted(arr, i) ;
    loop assigns i ;
    loop variant len-i ;
  */
  for(size_t i = 0 ; i < len ; ++i){
    //@ assert 0 < i ==> arr[i-1] <= arr[i] ;
  }
}


/*@ requires \valid_read(arr + (0 .. len-1));
    requires element_level_sorted(arr, len) ;
*/
unsigned bsearch_callee(int* arr, size_t len, int value){
  element_level_sorted_implies_sorted(arr, len) ;
  return bsearch(arr, len, value);
}
