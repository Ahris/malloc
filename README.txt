 __    __     ______     __         __         ______     ______    
/\ "-./  \   /\  __ \   /\ \       /\ \       /\  __ \   /\  ___\   
\ \ \-./\ \  \ \  __ \  \ \ \____  \ \ \____  \ \ \/\ \  \ \ \____  
 \ \_\ \ \_\  \ \_\ \_\  \ \_____\  \ \_____\  \ \_____\  \ \_____\ 
  \/_/  \/_/   \/_/\/_/   \/_____/   \/_____/   \/_____/   \/_____/ 
                                                                    
ABOUT

    Assignment for CSE 361 - System Software from my fall semester of 
    junior year.

    Lab instructions are included in the file:
    malloclab.pdf

    This implementation of malloc uses explicit seglists. The seglists 
    are sorted by last use and find fit uses first fit to find an 
    appropriate block to allocate. An allocated block has a word sized 
    header and footer to hold their size and allocated bit. A free block has a 
    3 word header and a single word footer to hold the size. Pointers are 
    passed around and are assumed to be referencing to the block's payload in 
    most cases. Coalesce is called every time we want to insert a block. 
    Realloc is implemented using mm_malloc and mm_free and checks for simple 
    edge cases.


AUTHOR

    Alice Wang
    Shyamolee Desai
    Nov 14, 2014
