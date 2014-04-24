/* 
 * Name: Pan Sun
 * Andrew ID: pans
 *
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */ 

#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */

char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    int row, col, i, j;
    int tmp, tmp0, tmp1, tmp2;
    int tmp3, tmp4, tmp5, tmp6; 

    /* diagnal elements cause confliction */
    if (M == 32 && N == 32) {
        for (row = 0; row < N; row += 8) {
            for (col = 0; col < M; col += 8) {
                for (i = row; i < row + 8; i++) {
                    for (j = col; j < col + 8; j++) {
                        if (i != j) {
                            tmp = A[i][j];
                            B[j][i] = tmp;
                        } 
                    }
                    // handle diagnal element after block access
                    if (row == col) {
                         tmp = A[i][i];
                         B[i][i] = tmp;
                    }
                }
            }
        }
    }

    /* 
     * 8*8 superBlock 4*8 subblocks 
     * store 4 value in extra variables to reduce miss 
     */
    if (M == 64 && N == 64) {
        for(col = 0; col < M; col += 8){
            for(row = 0; row < N; row += 8){
                for(i = 0; i < 8; i++){
                    for(j = 0; j < 4; j++){
                        if((col+j) != (row+i)){
                            B[col+j][row+i] = A[row+i][col+j];
                        }
                    } 
                    if(row == col){
                        B[col+i][row+i] = A[row+i][col+i]; 
                    }

                    // store values
                    if(i == 0){
                        tmp = A[row+i][col+4];
                        tmp0 = A[row+i][col+5];
                        tmp1 = A[row+i][col+6];
                        tmp2 = A[row+i][col+7];
                    }
                    if(i == 1){
                        tmp3 = A[row+i][col+4];
                        tmp4 = A[row+i][col+5];
                        tmp5 = A[row+i][col+6];
                        tmp6 = A[row+i][col+7];
                    }
                }
                for(i = 7; i > 1; i--){
                    for(j = 4; j < 8; j++){
                        if((col+j) != (row+i)){
                            B[col+j][row+i] = A[row+i][col+j];
                        }                      
                    }
                    if(row == col){
                        B[col+i][row+i] = A[row+i][col+i];
                    }
                }

                // put stored values at last
                B[col+4][row] = tmp;
                B[col+5][row] = tmp0;
                B[col+6][row] = tmp1;
                B[col+7][row] = tmp2; 
                B[col+4][row+1] = tmp3;
                B[col+5][row+1] = tmp4;
                B[col+6][row+1] = tmp5;
                B[col+7][row+1] = tmp6;
            }    
        }        
    }

    /* proper blocksize 16 */
    if (M == 61 && N == 67) {
        for (row = 0; row < N; row += 18) {
            for (col = 0; col < M; col += 18) {
                for (i = row; i < row + 18 && i < N; i++) {
                    for (j = col; j < col + 18 && j < M; j++){
                        tmp = A[i][j];
                        B[j][i] = tmp;
                    }
                }
            }
        }
    }
    ENSURES(is_transpose(M, N, A, B));
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;
    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}

