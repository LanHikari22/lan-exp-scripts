from typing import List, Any, Dict, TypeVar, Tuple, Union
from collections import defaultdict

T = TypeVar('T')
U = TypeVar('U')

# Could also take and preserve a generic n-tuple instead of `List[Any]`. 
def group_list_of_lists_by_col_with_append(lst: List[List[Any]], col: int) -> Dict[Any, List[List[Any]]]:
    mut_out = defaultdict(list)

    def get_list_without_col(lst: List[Any], col: int) -> List[Any]:
        if col >= len(lst):
            raise Exception(f'column {col} out of range')

        if len(lst) == 1:
            return []
        elif col == 0:
            return lst[1:]
        elif col == len(lst) - 1:
            return lst[:-1]
        else:
            return lst[:col] + lst[col+1:]

    for lst2 in lst:
        if col >= len(lst2):
            raise Exception(f'column {col} out of range')
        
        key = lst2[col]

        lst_without_col = get_list_without_col(lst2, col)

        for i, elem in enumerate(lst_without_col):
            if i >= len(mut_out[key]):
                mut_out[key].append([])
            
            mut_out[key][i].append(elem)

    return mut_out

def group_list_of_tup2_by_col_with_append(lst: List[Tuple[T, U]], col: int) -> Dict[Union[T, U], List[Union[T, U]]]:
    mut_dct = group_list_of_lists_by_col_with_append(lst, col)

    for key in mut_dct:
        if len(mut_dct[key]) != 1:
            raise Exception("We must have only two columns, so only one remaining")
        
        mut_dct[key] = mut_dct[key][0]
    
    return mut_dct