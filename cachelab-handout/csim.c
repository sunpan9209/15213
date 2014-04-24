/*
 *        Name : Pan Sun
 *   Andrew ID : pans
 */

#include "cachelab.h" 
#include <stdlib.h>
#include <getopt.h>
#include <unistd.h>
#include <stdio.h>

const int m = sizeof(long)*8;
int hitCount = 0, missCount = 0, evictCount = 0;
int s = 0, b = 0, E = 0, t = 0, vFlag = 0, hFlag = 0;
char *trace = NULL;

/*
 *  Cache is considered as a linked list of sets.
 *  Set is a linked list of Lines, with number of valid lines.
 *  Line has a flag, a tag and a pointer to the next line.
 * 	Add new line if no match.
 *  Evict the earliest line at the end if full.
 * 	Move matched line to the head as the latest added line.
 */

struct Line {
	int validFlag;
	unsigned tag;
	struct Line *nextLine;
};

struct Set {
	int maxLines;
	int numLines;
	struct Line *headLine;
	struct Set *nextSet;
};

/* setList initialization, return setList pointer*/
struct Set* initialSetList(int E, int s) {
    int numSets = (1 << s);
    struct Set *headSet;
    struct Set *set = (struct Set*)malloc(sizeof(struct Set));
    headSet = set;
  	set->maxLines = E;
  	set->numLines = 0;
  	set->headLine = NULL;
  	set->nextSet = NULL;
    for(int i = 1; i < numSets; i++) {
    	struct Set *nextSet = (struct Set*)malloc(sizeof(struct Set));
		nextSet->maxLines = E;
  		nextSet->numLines = 0;
  		nextSet->headLine = NULL;
  		nextSet->nextSet = NULL;
  		set->nextSet = nextSet;
  		set = nextSet;
    }	
    return headSet;
}

/* delete the last line */
void deleteLine(struct Set *set) {
	struct Line *current = set->headLine;
	struct Line *previous = NULL;
	if(current != NULL) {
		while(current->nextLine != NULL) {
			previous = current;
			current = current->nextLine;
		}
		if(previous == NULL) {
			set->headLine = NULL;
		}else {
			previous->nextLine = NULL;
		}
		set->numLines--;
		free(current);
	}
}

/* add line to the head of a set, may evict if full */
void addLine(struct Set *set, struct Line *line) {
	if(set->maxLines == set->numLines) {
		deleteLine(set);
		evictCount++;
		if(vFlag) {
			printf("eviction ");
		}
	}
	line->nextLine = set->headLine;
	set->headLine = line;
	set->numLines++;
}

/* fetch an address in the cache */
void fetch(struct Set *set, unsigned address){
	int tag = address >> (m-t);
	int setNum = ((1 << s)-1)&(address >> b);

	/* find the target set */
	for(int i = 0; i < setNum; i++) {
		set = set->nextSet;
	} 

	/* hit and return if tag matches */
	struct Line *line = set->headLine;
	struct Line *previous = NULL;
	while(line != NULL) {
		if(line->validFlag && (line->tag == tag)) {
			hitCount++;
			if(vFlag) {
				printf("hit ");
			}
			if(previous != NULL) {
				previous->nextLine = line->nextLine;
				line->nextLine = set->headLine;
				set->headLine = line;
			}
			return;
		}
		previous = line;
		line = line->nextLine;	
	}

	/* add new line if miss, eviction may happen*/
	missCount++;
	if(vFlag) {
		printf("miss ");
	}
	struct Line *newLine = (struct Line *)malloc(sizeof(struct Line));
	newLine->validFlag = 1;
	newLine->tag = tag;
	addLine(set,newLine);
}

/* free all lines and sets */
void freeSetList(struct Set *set) {
	while(set != NULL) {
		struct Line *line = set->headLine;
		while(line != NULL) {
			struct Line *tempLine = line->nextLine;
			free(line);
			line = tempLine;
		}
		struct Set *tempSet = set->nextSet;
		free(set);
		set = tempSet;
	}
}

/* set the parameters */
void setPara(int argc, char** argv) {
	int opt;
	while(-1 != (opt = getopt(argc, argv, "vhs:E:b:t:"))) {
		switch(opt) {
			case 'v':
				vFlag = 1;
				break;
			case 'h':
				hFlag = 1;
				break;
			case 's':
				s = atoi(optarg);
				break;
			case 'E':
				E = atoi(optarg);
				break;
			case 'b':
				b = atoi(optarg);
				break;
			case 't':
				trace = optarg;
				break;
			default:
				break;
		}
	}
	t = m - s - b;
}

int main(int argc, char** argv) {	
	char op;
	unsigned addr;
	int size;

	/* initialization */
    setPara(argc, argv);
	struct Set *set = initialSetList(E, s);

	/* read trace file */
	FILE *traceFile;
	traceFile = fopen(trace, "r");
	if(!traceFile) {
		printf("Error: Cann't open file %s!\n", trace);
		return -1;
	} 

	/* access the cache and print the result*/
	while(fscanf(traceFile, "%c %x, %d", &op, &addr, &size) > 0) {
		if(vFlag) {
			printf("%c %x, %d ", op, addr, size);
		}
		if((op == 'L')||(op == 'S')) {
			fetch(set, addr);
		}
		if(op == 'M') {
			fetch(set, addr);
			fetch(set, addr);
		}
		if(vFlag) {
			printf("\n");
		}
	}

	/* reset the cache */
	fclose(traceFile); 
	freeSetList(set);
	printSummary(hitCount, missCount, evictCount);
	return 0; 
}



