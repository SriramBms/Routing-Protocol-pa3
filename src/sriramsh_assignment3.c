/**
 * @sriramsh_assignment3
 * @author  Sriram Shantharam <sriramsh@buffalo.edu>
 * @version 1.0
 *
 * @section LICENSE
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation; either version 2 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details at
 * http://www.gnu.org/copyleft/gpl.html
 *
 * @section DESCRIPTION
 *
 * This contains the main function. Add further description here....
 */

// Reference:
// some of the code copied from Beej Guide to Network Programming

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "../include/global.h"
#include "../include/logger.h"
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <sys/stat.h>
#include <time.h>
#include <math.h>






#define TERM "***"
#define TRUE 1
#define FALSE 0
//#define DEBUG debug
#define DEBUG debug
#define MAX_NEIGHBORS 4
#define DISPLAY_FULL 1
#define DISPLAY_MINIMAL 2
#define STDIN 0
#define VERBOSE FALSE
int debug = TRUE;


//constants
#define UPDATE 1
#define STEP 2
#define PACKETS 3
#define DISPLAY 4
#define DISABLE 5
#define CRASH 6
#define DUMP 7
#define INTEGRITY 8
#define DEBUGLVL 9
#define COSTMAT 10
#define INVALID 0

//structures
//**Update packet format #1
//Each row is represented using one 32 bit integer
//32 bits is split into two 16 bit values based on the update packet format

struct node{
	uint32_t serverip;
	uint32_t serverport;
	uint32_t f_id_cost;
};

struct struct_update_packet {
	uint32_t f_upd_sport;
	uint32_t serverip;
	struct node nodes[5];
};

//**Distance vector routing table format

struct routing_entry{
	char destip[HOSTNAME_LEN];
	uint16_t port;
	uint16_t destid;
	uint16_t cost;
	uint16_t nexthop;
	int connected;
	int valid;
	int num_tries;

};

struct struct_routing_table{
	char selfip[HOSTNAME_LEN];
	uint16_t selfid;
	uint16_t port;

	struct routing_entry othernodes[MAX_NEIGHBORS+1];
};



//global variables
char t_file_name[FILEPATH_LEN]; //topology file name
float r_update_interval; // routing update interval
int num_servers;
int num_edges;
struct struct_routing_table routing_table = {0}, init_costs = {0};

struct routing_entry sorted_table[MAX_NEIGHBORS+1] = {0};
int routing_update_counter=0;
int local_id;
fd_set master, readfds;
int fdmax;
int yes = 1;
char * tokenptr;
int num_received_packets=0;
double runtime_timeout;
int reset_the_timer=TRUE;
struct struct_update_packet update_packet = {0};
int node_matrix[MAX_NEIGHBORS+1][MAX_NEIGHBORS+1]={0};
struct timeval starttime, endtime;
//function declarations
void zprintf(char *);
void read_topology_file();
void parse_server_details(char* , int);
void dump_routing_table(int);
void parse_link_details(char*, int);
void fill_empty_fields();
int getCommandType(char *);
void strToLower(char *);
void loop_small();
void send_updates();
int get_cost_for_id(int);
void print_cost_matrix();
int get_routing_table_index_for_id(int);
//functions

void loop_small(){
	int i=0;
	while(i<1000){
		i++;
	}
}

void strToLower(char string[]) {

	int i;

	for (i = 0; string[i] != '\0'; i++)
		string[i] = (char)tolower(string[i]);


}



void toggleDebugLevel(){
	if(DEBUG)
		debug = FALSE;
	else
		debug = TRUE;
}

int getCommandType(char * token){
	strToLower(token);
	if(strcmp(token,"update")==0)
		return UPDATE;
	else if(strcmp(token, "step")==0)
		return STEP;
	else if(strcmp(token, "display")==0)
		return DISPLAY;
	else if(strcmp(token, "debug")==0)
		return DEBUGLVL;
	else if(strcmp(token, "packets")==0)
	  return PACKETS;
	else if(strcmp(token, "disable")==0)
		return DISABLE;
	else if(strcmp(token, "crash")==0)
		return CRASH;
	else if(strcmp(token, "dump")==0)
		return DUMP;
	else if(strcmp(token, "academic_integrity")==0)
		return INTEGRITY;
	else if(strcmp(token, "costmat")==0)
		return COSTMAT;
	else
		return INVALID;
}

void dump_routing_table(int mode){
	int ii;
	for(ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		sorted_table[ii].destid = routing_table.othernodes[ii].destid;
		sorted_table[ii].cost = routing_table.othernodes[ii].cost;
		sorted_table[ii].nexthop = routing_table.othernodes[ii].nexthop;

		if(DEBUG){
			fprintf(stderr, "DUMP TABLE: destid: %d, cost %d, nexthop: %d \n", sorted_table[ii].destid, sorted_table[ii].cost, sorted_table[ii].nexthop);
		}
	}

	for(ii = 0; ii < MAX_NEIGHBORS; ii++){
		int jj;
		for(jj = ii+1; jj < MAX_NEIGHBORS+1; jj++){
			if(sorted_table[jj].destid < sorted_table[ii].destid){

				uint16_t tmp;
				tmp = sorted_table[ii].destid;
				sorted_table[ii].destid = sorted_table[jj].destid;
				sorted_table[jj].destid = tmp;

				tmp = sorted_table[ii].cost;
				sorted_table[ii].cost = sorted_table[jj].cost;
				sorted_table[jj].cost = tmp;

				tmp = sorted_table[ii].nexthop;
				sorted_table[ii].nexthop = sorted_table[jj].nexthop;
				sorted_table[jj].nexthop = tmp;

			}
		}
	}

	for(ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		if(mode == DISPLAY_MINIMAL)
			//fprintf(stderr, "%-15d%-15d%-15d\n", sorted_table[ii].destid, sorted_table[ii].nexthop, sorted_table[ii].cost);
			if(sorted_table[ii].nexthop == UINT16_MAX){
				cse4589_print_and_log("%-15d%-15d%-15d\n", sorted_table[ii].destid, -1, sorted_table[ii].cost);
			}else{
				cse4589_print_and_log("%-15d%-15d%-15d\n", sorted_table[ii].destid, sorted_table[ii].nexthop, sorted_table[ii].cost);
			}
		else if(mode == DISPLAY_FULL){
		 //fprintf(stderr, "%-15d%-15d%-15d%-15d%-15s\n", sorted_table[ii].destid, sorted_table[ii].nexthop, sorted_table[ii].cost, sorted_table[ii].port, sorted_table[ii].destip);
			cse4589_print_and_log("%-15d%-15d%-15d\n", sorted_table[ii].destid, sorted_table[ii].nexthop, sorted_table[ii].cost);
		}else{
			//:|
		}
	}
}

void fill_empty_fields(){
	zprintf("In fill_empty_fields");
	int ii;
	for(ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		zprintf("outer loop");
		if(routing_table.othernodes[ii].connected != TRUE){
			zprintf("inside if");
			if(routing_table.othernodes[ii].destid==local_id){
				routing_table.othernodes[ii].cost = 0;
				routing_table.othernodes[ii].nexthop = local_id;
				if(DEBUG){
					fprintf(stderr, "FEF: cost: %d, nexthop: %d \n", routing_table.othernodes[ii].cost, routing_table.othernodes[ii].nexthop);
				}
			}else{
				routing_table.othernodes[ii].cost = UINT16_MAX;
				routing_table.othernodes[ii].nexthop = -1;
				if(DEBUG){
					fprintf(stderr, "FEF: cost: %d, nexthop: %d \n", routing_table.othernodes[ii].cost, routing_table.othernodes[ii].nexthop);
				}
			}
		}
	}



//	dump_routing_table(DISPLAY_FULL);
	//dump_routing_table(DISPLAY_MINIMAL);
}


void parse_link_details (char * i_string, int strlen){

	/* reference
	struct routing_entry{
		char destip[HOSTNAME_LEN];
		uint16_t port;
		uint16_t destid;
		uint16_t cost;
		uint16_t nexthop;
		int connected;
	};
	*/
	zprintf("In parse_link_details");
	char * tokptr;
	uint16_t tempval;

	tempval = (uint16_t)atoi(strtok_r(i_string, " ", &tokptr));
	if(DEBUG){
		fprintf(stderr,"server id: %d, local id: %d \n", tempval, local_id);
	}
	if(tempval != (uint16_t)local_id){
		fprintf(stderr, "Error while reading link costs \n");
		exit(2);
	}
	tempval = (uint16_t)atoi(strtok_r(NULL, " ", &tokptr));
	int ii;
	for(ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		if(routing_table.othernodes[ii].destid == tempval){
			routing_table.othernodes[ii].cost = (uint16_t)atoi(strtok_r(NULL, " ", &tokptr));
			routing_table.othernodes[ii].nexthop = tempval;
			routing_table.othernodes[ii].connected = TRUE;
			routing_table.othernodes[ii].valid = TRUE;
			routing_table.othernodes[ii].num_tries = 0;
		}
	}

}


void parse_server_details(char * i_string, int strlen){
	zprintf("In parse_server_details");
	if(DEBUG){
		fprintf(stderr,"Received string: %s \n",i_string);
	}
	char * tokptr;
	char tmp_destip[HOSTNAME_LEN];
	uint16_t tmp_destid;
	//routing_table.othernodes[loc].destid = (uint16_t)atoi(strtok_r(i_string, " ", &tokptr));
	tmp_destid = (uint16_t)atoi(strtok_r(i_string, " ", &tokptr));

	//strcpy(routing_table.othernodes[loc].destip, strtok_r(NULL, " ", &tokptr));
	strcpy(tmp_destip, strtok_r(NULL, " ", &tokptr));
	if(strcmp(routing_table.selfip, tmp_destip)==0){
		local_id = (int)tmp_destid;
		routing_table.selfid = tmp_destid;

		if(DEBUG){
			fprintf(stderr, "local id: %d \n", local_id);
			//fprintf(stderr, "Packet dump: %s \n", routing_table);
		}
		//routing_table.othernodes[routing_update_counter].destid = tmp_destid;
		//strcpy(routing_table.othernodes[routing_update_counter].destip, tmp_destip);
		//routing_table.othernodes[routing_update_counter].port = (uint16_t)atoi(strtok_r(NULL, " ", &tokptr));
		/*
		if(DEBUG){
			fprintf(stderr, "SELF ID: %d destid: %d, destIP: %s, destport: %d \n", local_id, routing_table.othernodes[routing_update_counter].destid, routing_table.othernodes[routing_update_counter].destip, routing_table.othernodes[routing_update_counter].port);
			//fprintf(stderr, "Packet dump: %s \n", routing_table);
		}
		return;
		*/
	}

	routing_table.othernodes[routing_update_counter].destid = tmp_destid;
	zprintf("Done: destid");
	strcpy(routing_table.othernodes[routing_update_counter].destip, tmp_destip);
	zprintf("Done: destIP");
	routing_table.othernodes[routing_update_counter].port = (uint16_t)atoi(strtok_r(NULL, " ", &tokptr));
	zprintf("Done: port");
	if(strcmp(routing_table.selfip, tmp_destip)==0){
		routing_table.port = routing_table.othernodes[routing_update_counter].port;
	}

	if(DEBUG){
		fprintf(stderr, "destid: %d, destIP: %s, destport: %d \n", routing_table.othernodes[routing_update_counter].destid, routing_table.othernodes[routing_update_counter].destip, routing_table.othernodes[routing_update_counter].port);
		//fprintf(stderr, "Packet dump: %s \n", routing_table);
	}
	routing_update_counter++; //reset this before calling this function
}


void read_topology_file(){
	FILE *fp;
	if((fp = fopen(t_file_name, "r"))==NULL){
		fprintf(stderr, "Topology file open failed\n");
		exit(2);
	}

	char c1_tmp[2];
	char s_tmp[50];
	c1_tmp[0] = getc(fp);
	c1_tmp[1] = '\0';
	if(DEBUG){
		fprintf(stderr, "read char value: %s \n", c1_tmp);
	}

	num_servers = (int) atoi(c1_tmp);
	if(fseek(fp, 1, SEEK_CUR)==-1){
		fprintf(stderr, "Topology file fseek failed\n");
		exit(2);
	}
	c1_tmp[0] = getc(fp);
	c1_tmp[1] = '\0';
	num_edges = (int) atoi(c1_tmp);
	if(DEBUG){
		fprintf(stderr, "num servers: %d, num edges: %d \n", num_servers, num_edges);
	}

	if(fseek(fp, 1, SEEK_CUR)==-1){
		fprintf(stderr, "Topology file fseek failed\n");
		exit(2);
	}

	int server_loop = 0;
	routing_update_counter = 0;
	while(server_loop < num_servers){
		if(DEBUG){
			fprintf(stderr, "Server Loop %d\n", server_loop);
		}
		int ii = 0;
		int string_len = 0;
		memset(s_tmp, 0, 50);
		while((s_tmp[ii]=getc(fp))!='\n'){
			string_len++;
			ii++;
		//	zprintf("Looping...");
		}
		zprintf("Done looping");
		s_tmp[string_len]='\0';
		zprintf("Parsing server details");
		parse_server_details(s_tmp, string_len);

		server_loop++;
	}

	int link_loop = 0;
	while(link_loop < num_edges){
		if(DEBUG){
			fprintf(stderr, "Link Loop %d\n", link_loop);
		}
		int ii = 0;
		int string_len = 0;
		memset(s_tmp, 0, 50);
		while((s_tmp[ii]=getc(fp))!='\n'){
			string_len++;
			ii++;
		//	zprintf("Looping...");
		}
		zprintf("Done looping");
		s_tmp[string_len]='\0';
		zprintf("Parsing server details");
		parse_link_details(s_tmp, string_len);
		link_loop++;
	}

	fill_empty_fields();
	init_costs = routing_table;

	//setup the cost matrix
	int j,k;
	for(j = 0;j < num_servers; j++){
		if((j+1) == routing_table.selfid){
			for(k = 0; k < num_servers; k++){
				node_matrix[j][k] = get_cost_for_id(k+1);
			}
		}
	}

 if(DEBUG){
	print_cost_matrix();
 }

}

int get_cost_for_id(int id){
	int j;
	for(j = 0;j < MAX_NEIGHBORS + 1; j++){
		if(routing_table.othernodes[j].destid == id){
			return routing_table.othernodes[j].cost;
		}
	}
}


int get_cost_to_node(int id){
	int j;
	for(j = 0; j < MAX_NEIGHBORS + 1; j++){
		if(init_costs.othernodes[j].destid == id){
			return init_costs.othernodes[j].cost;
		}
	}
}
void print_cost_matrix(){
	int j,k;
	for(j = 0; j < num_servers; j++){
		for(k = 0; k < num_servers; k++){
			fprintf(stderr, "|   %d ", node_matrix[j][k]);
		}
			fprintf(stderr, "\n");
	}
}


void zprintf(char * msg){
	if(DEBUG){
		fprintf(stderr, "%s\n", msg);
	}
}

void getMyIP(char * buf){
	char dnsServer[] = "8.8.8.8"; //or any valid ip. Get one using getHostIP()
	int status;
	int fd;
	struct sockaddr_in dnsaddr,myaddr;
	int myaddrlen;


	if((fd=socket(AF_INET,SOCK_DGRAM,0))<0){
		fprintf(stderr,"Error while creating socket %d",fd);
		exit(21);
	}

	dnsaddr.sin_family = AF_INET;
	dnsaddr.sin_addr.s_addr = inet_addr(dnsServer);
	dnsaddr.sin_port = htons(53);



	if((status=connect(fd, (struct sockaddr *)&dnsaddr, sizeof dnsaddr))<0){
		fprintf(stderr,"Error while connecting... %d",status);
		exit(22);

	}
	myaddrlen = sizeof(myaddr);
	if((status = getsockname(fd,(struct sockaddr *)&myaddr,&myaddrlen))){
		fprintf(stderr,"Error while getting local ip %d",status);
		exit(23);

	}

	strcpy(buf,inet_ntoa(myaddr.sin_addr));
	close(fd);


}

void send_udp_msg(char * i_ip, int i_port){
	struct addrinfo hints, *ai, *p;


	struct sockaddr_storage remoteaddr;
	socklen_t addrlen;
	char buf[256];
	int nbytes;
	char remoteIP[INET6_ADDRSTRLEN];
	int i,j,rv;

	if(DEBUG)
	fprintf(stderr,"In send_udp_msg*** Sending udp to %s\n", i_ip);



	memset(&hints,0, sizeof hints);
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_DGRAM;
	hints.ai_flags = AI_PASSIVE;
	char str_port[5];


		memset(&str_port, 0, 5);
		sprintf(str_port, "%d", i_port);
		if(DEBUG)
		fprintf(stderr,"str_port:%s \n", str_port);
		if((rv=getaddrinfo(i_ip,str_port,&hints,&ai)) != 0){
			fprintf(stderr,"selectserver: %s \n", gai_strerror(rv));
			exit(3);
		}

		int sfd = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
		if(sfd == -1){
			perror("Error while creating socket \n");
			exit(4);
		}
		/*
		if(setsockopt(sfd,SOL_SOCKET,SO_REUSEADDR,&yes,sizeof(int))<0){
			perror("Error while setting socket for reuse\n");
			exit(5);
		}
		*/
		int bytessent;
		/*
		if((bytessent = sendto(sfd, i_msg, strlen(i_msg), 0, ai->ai_addr, ai->ai_addrlen))==-1){
				perror("Error while sending bytes");
		}
		*/
		if((bytessent = sendto(sfd, &update_packet, sizeof update_packet, 0, ai->ai_addr, ai->ai_addrlen))==-1){
				perror("Error while sending bytes");
		}

		if(bytessent != sizeof (update_packet)){
			fprintf(stderr, "Partial packet sent\n");
		}

		if(DEBUG){
			fprintf(stderr, "bytes sent: %d\n", bytessent);
		}
		freeaddrinfo(ai);




}

int is_ip_valid(char * i_ip){
	int j;
	for(j = 0; j < MAX_NEIGHBORS + 1; j++){
		if(strcmp(routing_table.othernodes[j].destip, i_ip)==0){
			if(routing_table.othernodes[j].valid)
				return TRUE;
			else
				return FALSE;
		}
	}
}

int get_id_for_ip(char * i_ip){
	int j;
	for(j = 0; j < MAX_NEIGHBORS + 1; j++){
		if(strcmp(routing_table.othernodes[j].destip, i_ip)==0){
			return routing_table.othernodes[j].destid;
		}
	}
}
void create_update_packet(){
	update_packet.f_upd_sport = (uint16_t)num_servers;
	/*
	if(DEBUG){
		fprintf(stderr,"f_upd_sport: %d: %x \n", (int)update_packet.f_upd_sport, (int)update_packet.f_upd_sport);
	}
	*/
	update_packet.f_upd_sport = update_packet.f_upd_sport << 16;
	/*
	if(DEBUG){
		fprintf(stderr,"f_upd_sport: %d: %x \n", (int)update_packet.f_upd_sport, (int)update_packet.f_upd_sport);
	}
	*/
	update_packet.f_upd_sport = update_packet.f_upd_sport | routing_table.port;

	struct sockaddr_in sa;
	inet_pton(AF_INET, routing_table.selfip, &(sa.sin_addr));
	update_packet.serverip = sa.sin_addr.s_addr;
	if(DEBUG){
		fprintf(stderr,"f_upd_sport: %d: %x , serverip: %d\n", (int)update_packet.f_upd_sport, (int)update_packet.f_upd_sport, sa.sin_addr.s_addr);
	}
	int ii;
	for(ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		struct sockaddr_in sn;
		inet_pton(AF_INET, routing_table.othernodes[ii].destip, &(sn.sin_addr));
		update_packet.nodes[ii].serverip = sn.sin_addr.s_addr;
		update_packet.nodes[ii].serverport = routing_table.othernodes[ii].port;
		update_packet.nodes[ii].serverport = update_packet.nodes[ii].serverport << 16;
		update_packet.nodes[ii].f_id_cost = routing_table.othernodes[ii].destid;
		update_packet.nodes[ii].f_id_cost = update_packet.nodes[ii].f_id_cost << 16;
		update_packet.nodes[ii].f_id_cost = update_packet.nodes[ii].f_id_cost | routing_table.othernodes[ii].cost;

	}

}



void parse_update_packet(char * i_msg){
	struct struct_update_packet recvupdpkt = {0};
	memcpy(&recvupdpkt, i_msg, sizeof recvupdpkt);
	int num_fields = recvupdpkt.f_upd_sport >> 16;
	int source_port = (recvupdpkt.f_upd_sport << 16)>>16;
	char source_addr[INET6_ADDRSTRLEN]={0};
	struct sockaddr_in rsn;
	rsn.sin_addr.s_addr = recvupdpkt.serverip;
	inet_ntop(AF_INET, &(rsn.sin_addr), source_addr, sizeof source_addr);



	if(DEBUG){
		//display contents of packet
		fprintf(stderr, "Contents of received packet\n");
		fprintf(stderr, "Received: f_upd_sport: %d, ip: %d\n", recvupdpkt.f_upd_sport, recvupdpkt.serverip);
		fprintf(stderr, "num fields: %d, server port: %x, server ip %s\n", num_fields, source_port, source_addr);
	}

	if(!is_ip_valid(source_addr))
		return;

	int j;

	uint32_t ipaddress_list[5];
	int port_list[5];
	int cost_list[5];
	int n_server_id;
	if(DEBUG)
		fprintf(stderr, "parsing neighbor costs\n");
	for(j = 0; j < num_fields; j++){
		n_server_id = (recvupdpkt.nodes[j].f_id_cost >> 16);
		ipaddress_list[n_server_id - 1] = recvupdpkt.nodes[j].serverip;
		port_list[n_server_id - 1] = (recvupdpkt.nodes[j].serverport >> 16);
		int costN = (recvupdpkt.nodes[j].f_id_cost <<  16) >> 16;
		cost_list[n_server_id - 1] = costN;
		/*
		if(costN == UINT16_MAX)
			cost_list[n_server_id - 1] = 9999;
			*/
		if(DEBUG){
			fprintf(stderr, " ++++++id: %d ipaddr: %d port %d cost %d\n",n_server_id, ipaddress_list[n_server_id - 1],port_list[n_server_id - 1],cost_list[n_server_id - 1]);

		}

	}

	//+++++++++ run DV algo +++++++++++++//

	int CostToN = get_cost_to_node(get_id_for_ip(source_addr));
	if(DEBUG){
		fprintf(stderr, "neighbor id: %d \n", get_id_for_ip(source_addr));
	}
	int DnToY;
	for(j = 0; j < num_fields; j++){
		if((j+1)==routing_table.selfid)
			continue;
		DnToY = cost_list[j];
		long sum = CostToN + DnToY;
		if(DEBUG){
			fprintf(stderr, "---------- id: %d, DnToY: %d, costToN: %d, sum: %ld\n", j+1, DnToY, CostToN, sum);
		}
		if(DEBUG){
			fprintf(stderr, "node_matrix: %d\n", node_matrix[routing_table.selfid-1][j]);
		}

		if((CostToN + DnToY) <= node_matrix[routing_table.selfid-1][j]){
			node_matrix[routing_table.selfid-1][j] = (CostToN + DnToY);
			int index = get_routing_table_index_for_id(j+1);
			routing_table.othernodes[index].nexthop = get_id_for_ip(source_addr);
			routing_table.othernodes[index].cost = (CostToN + DnToY);
			if(DEBUG){
				fprintf(stderr, "---------recv sum < present sum| index: %d routetbl nexthop: %d cost %d\n", index,routing_table.othernodes[index].nexthop,routing_table.othernodes[index].cost  );
			}

		}
		if(DEBUG){
			fprintf(stderr, "---------QQQQQQQ| routetbl nexthop: %d cost %d\n", routing_table.othernodes[get_routing_table_index_for_id(3)].nexthop,routing_table.othernodes[get_routing_table_index_for_id(3)].cost  );
		}
	}

}

int get_routing_table_index_for_id(int id){
	int j;
	for(j = 0; j < MAX_NEIGHBORS; j++){
		if(routing_table.othernodes[j].destid == id){
			return j;
		}
	}
}


void send_updates(){
	create_update_packet();
	int ii = 0;
	for (ii = 0; ii < MAX_NEIGHBORS+1; ii++){
		if(routing_table.othernodes[ii].connected){
			send_udp_msg(routing_table.othernodes[ii].destip, routing_table.othernodes[ii].port);
		}
	}

}
double get_current_time(){
	struct timeval cur_time;
	gettimeofday(&cur_time, NULL);
	double current_time = cur_time.tv_sec + (cur_time.tv_usec)/1000000;
	if(DEBUG){
		fprintf(stderr, "Current time: %g", current_time);
	}
	return current_time;
}

void init(){
	getMyIP(routing_table.selfip);
	if(DEBUG){
		fprintf(stderr, "Local Ip: %s \n", routing_table.selfip);
	}

}//end of init
/**
 * main function
 *
 * @param  argc Number of arguments
 * @param  argv The argument list
 * @return 0 EXIT_SUCCESS
 */
int main(int argc, char **argv)
{
	/*Init. Logger*/
	cse4589_init_log();

	/*Clear LOGFILE and DUMPFILE*/
	fclose(fopen(LOGFILE, "w"));
	fclose(fopen(DUMPFILE, "wb"));

	/*Start Here*/
	init();
	if(argc<4){
		fprintf(stderr,"1-Invalid Arguments \n Usage %s -t <path-to-topology-file> -i <routing-update-interval>\n", argv[0] );
		exit(1) ;
	}

	if(strncmp(argv[1],"-t",2)==0){
		strncpy(t_file_name,argv[2],FILEPATH_LEN);
		if(strncmp(argv[3],"-i",2)==0){
			char update_interval[10];
			strcpy(update_interval, argv[4]);
			r_update_interval = (float)atof(update_interval);
		}else{
			fprintf(stderr,"2-Invalid Arguments \n Usage %s -t <path-to-topology-file> -i <routing-update-interval>\n", argv[0] );
			exit(1) ;
		}

	}else if(strncmp(argv[1],"-i",2)==0){
		char update_interval[10];
		strcpy(update_interval, argv[2]);
		if(DEBUG){
			fprintf(stderr, "Update interval string: %s \n", update_interval);
		}
		r_update_interval = (float)atof(update_interval);

		if(strncmp(argv[3],"-t",2)==0){
			strncpy(t_file_name,argv[4],FILEPATH_LEN);
		}else{
			fprintf(stderr,"3-Invalid Arguments \n Usage %s -t <path-to-topology-file> -i <routing-update-interval>\n", argv[0] );
			exit(1) ;
		}

	}else{
		fprintf(stderr,"4-Invalid Arguments \n Usage %s -t <path-to-topology-file> -i <routing-update-interval>\n", argv[0] );
		exit(1) ;
	}

	if(DEBUG){
		fprintf(stderr, "Arguments: File name: %s Update interval %f \n", t_file_name, r_update_interval);
	}
	runtime_timeout = r_update_interval;
	read_topology_file();


	struct addrinfo hints, *ai, *p;
	char command[200]={0};
	char tokencommand[50]={0};
	int listener;
	int newfd;
	struct sockaddr_storage remoteaddr;
	socklen_t addrlen;
	char buf[256];
	int nbytes;
	char remoteIP[INET6_ADDRSTRLEN];
	int i,j,rv;
	FD_ZERO(&master);
	FD_ZERO(&readfds);
	int select_result=0;
	//local vars





	memset(&hints,0, sizeof hints);
	hints.ai_family = AF_INET;
	hints.ai_socktype = SOCK_DGRAM;
	hints.ai_flags = AI_PASSIVE;
	char str_port[5];

 	sprintf(str_port, "%d", (int)routing_table.port);
	if(DEBUG)
		fprintf(stderr,"str_port:%s \n", str_port);
	if((rv=getaddrinfo(NULL,str_port,&hints,&ai)) != 0){
		fprintf(stderr,"selectserver: %s \n", gai_strerror(rv));
		exit(3);
	}

	listener = socket(ai->ai_family, ai->ai_socktype, ai->ai_protocol);
	if(listener < 0){
		perror("Error while creating socket \n");
		exit(4);
	}


	if(setsockopt(listener,SOL_SOCKET,SO_REUSEADDR,&yes,sizeof(int))<0){
		perror("Error while setting socket for reuse\n");
		exit(5);
	}


	if(bind(listener,ai->ai_addr,ai->ai_addrlen)<0){
		close(listener);
		perror("Error while binding\n");
		exit(44);
	}

	freeaddrinfo(ai);
	/*
	if (listen(listener, 10) == -1) {  //Lister to clients if running as a server!
		perror("listen");
		exit(5);
	}
	*/

	if(DEBUG){
		int retval;
		socklen_t len = sizeof(retval);
		if (getsockopt(listener, SOL_SOCKET, SO_ACCEPTCONN, &retval, &len) == -1)
			printf("fd %d is not a socket\n", listener);
		else if (retval)
			printf("fd %d is a listening socket. Returned %d\n", listener,retval);
		else
			printf("fd %d is a non-listening socket. Returned %d\n", listener,retval);

	}
	FD_SET(STDIN,&master);
	FD_SET(listener,&master);
	fdmax = listener;
	runtime_timeout = r_update_interval;

	dump_routing_table(DISPLAY_MINIMAL);
	print_cost_matrix();
	for(;;){
		FD_ZERO(&readfds);
		readfds = master;
		struct timeval select_timeout;






/*

double w_num = (double)(runtime_timeout);


select_timeout.tv_sec = (time_t)w_num;
select_timeout.tv_usec = 0;
gettimeofday(&starttime,NULL);
*/
		//++++++++++++++++++++++++

	  if(reset_the_timer){



		double w_num = (double)(r_update_interval);


		select_timeout.tv_sec = (time_t)w_num;
		select_timeout.tv_usec = 0;
		gettimeofday(&starttime,NULL);
	}else{
		double w_num = (double)(runtime_timeout);


		select_timeout.tv_sec = (time_t)w_num;
		select_timeout.tv_usec = 0;
		//gettimeofday(&starttime,NULL);
	}

		//++++++++++++++++++++++++









		if((select_result=select(fdmax+1,&readfds,NULL,NULL,&select_timeout))==-1){
			perror("SELECT failed");
			exit(6);
		}
		zprintf("select fired");
		if(select_result == 0){
			runtime_timeout = r_update_interval;
			zprintf("1");
			send_updates();

			continue;
		}
		//fprintf(stderr,"\n >>> \n");

		for(i=0;i<=fdmax;i++){
			reset_the_timer = FALSE;
			//fprintf(stderr, "checking fd %d\n",i);
			if(FD_ISSET(i,&readfds)){
				if(VERBOSE)
					printf("fd set for %d\n",i);
				if(i==STDIN){
					FD_CLR(0,&readfds);
					fgets(command, sizeof (command),stdin);
					int len = strlen(command) - 1;
					if(DEBUG)
						fprintf(stderr, "from stdin: %s\n", command);
					//fprintf(stderr,"Length=%d",len);
					if(len==0){
						zprintf("len 0");
						//gettimeofday(&endtime,NULL);
					//	runtime_timeout = (double)(r_update_interval -endtime.tv_sec + starttime.tv_sec);
						continue;
					}

					if (command[len] == '\n')
						command[len] = '\0';

					//strToLower(command);

					//fprintf(stderr,"Input: %s\n",command);

					strcpy(tokencommand,strtok_r(command," ",&tokenptr));
					/*
					if(strlen(tokencommand)<1){
						FD_CLR(0,&readfds);
						zprintf("2");
						continue;
					}

					if(tokencommand==NULL ||tokencommand=='\0'){
						//fprintf(stderr,"enterpressed\n\n");
						FD_CLR(0,&readfds);
						zprintf("3");
						continue;
					}
					*/
					int commandtype = getCommandType(tokencommand);
					if(DEBUG){
						fprintf(stderr, "commandtype: %d \n", commandtype);
					}
					switch (commandtype){
						case DISPLAY:
							cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							dump_routing_table(DISPLAY_MINIMAL);
							break;
						case DEBUGLVL:
							//cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							toggleDebugLevel();
							break;
						case UPDATE:
							;
							cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							char infstr[3];
							uint16_t server1 = atoi(strtok_r(NULL, " ", &tokenptr));
							uint16_t server2 = atoi(strtok_r(NULL, " ", &tokenptr));
							strncpy(infstr, strtok_r(NULL, " ", &tokenptr), 3);
							uint16_t newcost = atoi(infstr);

							if(strcmp(infstr, "inf")==0)
								newcost = UINT16_MAX;
							uint16_t targetid;
							if(server1 == local_id && server2 != local_id){
								targetid = server2;
							}else{
								fprintf(stderr, "Wrong input. Please try again\n");

							}
							routing_table = init_costs;
							int ii;
							for (ii = 0; ii < MAX_NEIGHBORS+1; ii++){
								if(routing_table.othernodes[ii].destid == targetid)
									routing_table.othernodes[ii].cost = newcost;
							}
							init_costs = routing_table;
							send_updates();

							break;
						case PACKETS:
							cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							cse4589_print_and_log("%d\n",num_received_packets);
							num_received_packets = 0;
							break;
						case STEP:
							cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							/*create_update_packet();
							send_udp_msg(routing_table.othernodes[3].destip, routing_table.othernodes[3].port);
							*/
							zprintf("2");
							send_updates();
							break;
						case DISABLE:
							break;
						case CRASH:
							break;
						case DUMP:
							break;
						case INTEGRITY:
							cse4589_print_and_log("%s:SUCCESS\n",tokencommand);
							cse4589_print_and_log("I have read and understood the course academic integrity policy \nlocated at http://www.cse.buffalo.edu/faculty/dimitrio/courses/cse4589_f14/index.html#integrity\n");
							break;
						case COSTMAT:
							print_cost_matrix();
							break;
						default:
							;
							char * invalidmsg = "Invalid command Please try again";
							cse4589_print_and_log("%s:%s \n",tokencommand,invalidmsg);
							//do something
					}
				}else if(i==listener){
					FD_CLR(listener, &readfds);
					fprintf(stderr, "Received something\n");
					char newMessage[1024];
					int bytesrecvd = recvfrom(listener, newMessage, sizeof newMessage, 0, NULL, NULL);
					if(DEBUG){
						fprintf(stderr, "bytes received: %d\n", bytesrecvd);
					}
					num_received_packets++;

					parse_update_packet(newMessage);

					dump_routing_table(DISPLAY_MINIMAL);
					print_cost_matrix();
				}else{

				}
			}
		}
		//zprintf("tag");
		/*
		gettimeofday(&endtime,NULL);
		if(DEBUG){
			fprintf(stderr, "end-start: %g\n",(double)(endtime.tv_sec - starttime.tv_sec));
		}
		if((endtime.tv_sec - starttime.tv_sec)>=r_update_interval){
			if(DEBUG){
				fprintf(stderr, "e-s: %g, r_u_i: %g\n", (double)(endtime.tv_sec - starttime.tv_sec), r_update_interval);
			}
			runtime_timeout = r_update_interval;
			zprintf("3");
			send_updates();

		}else{
			zprintf("4");

		runtime_timeout = (double)(r_update_interval -(endtime.tv_sec - starttime.tv_sec));

		}
		*/

		if(reset_the_timer == FALSE){
			gettimeofday(&endtime,NULL);
			long duration = (endtime.tv_sec - starttime.tv_sec);
			if(duration > r_update_interval){
				send_updates();
				reset_the_timer = TRUE;
			}else{
				runtime_timeout = (double)(r_update_interval -(endtime.tv_sec - starttime.tv_sec));
				if(runtime_timeout < 1.0){
					send_updates();
					reset_the_timer = TRUE;

				}
			}
		}


	}


	return 0;
}
