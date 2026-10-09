/*-
 * Copyright (c) 2018 Matthew Naylor
 * Copyright (c) 2018 Jonathan Woodruff
 * Copyright (c) 2018 Alexandre Joannou
 * Copyright (c) 2018 Hesham Almatary
 * All rights reserved.
 *
 * This software was developed by SRI International and the University of
 * Cambridge Computer Laboratory (Department of Computer Science and
 * Technology) under DARPA contract HR0011-18-C-0016 ("ECATS"), as part of the
 * DARPA SSITH research programme.
 *
 * This software was partly developed by the University of Cambridge
 * Computer Laboratory as part of the Partially-Ordered Event-Triggered
 * Systems (POETS) project, funded by EPSRC grant EP/N031768/1.
 *
 * @BERI_LICENSE_HEADER_START@
 *
 * Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
 * license agreements.  See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.  BERI licenses this
 * file to you under the BERI Hardware-Software License, Version 1.0 (the
 * "License"); you may not use this file except in compliance with the
 * License.  You may obtain a copy of the License at:
 *
 *   http://www.beri-open-systems.org/legal/license-1-0.txt
 *
 * Unless required by applicable law or agreed to in writing, Work distributed
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * @BERI_LICENSE_HEADER_END@
 */

#include <netinet/in.h>
#include <arpa/inet.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <ctype.h>
#include <assert.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <assert.h>
#include <signal.h>
#include <string.h>

// API
////////////////////////////////////////////////////////////////////////////////
#ifdef __cplusplus
extern "C" {
#endif
  extern unsigned long long serv_socket_create(const char * name, unsigned int dflt_port);
  extern unsigned long long serv_socket_create_nameless(unsigned int dflt_port);
  extern inline void serv_socket_init(unsigned long long ptr);
  extern uint32_t serv_socket_get8(unsigned long long ptr);
  extern uint8_t serv_socket_put8(unsigned long long ptr, uint8_t byte);
  extern uint8_t serv_socket_put8_blocking(unsigned long long ptr, uint8_t byte);
  extern void serv_socket_getN(void* result, unsigned long long ptr, int nbytes);
  extern uint8_t serv_socket_putN(unsigned long long ptr, int nbytes, unsigned int* data);
#ifdef __cplusplus
}
#endif

// General helpers
////////////////////////////////////////////////////////////////////////////////
#define STR_BUFF_SZ 256

int getPortNumber(const char * name, unsigned int dflt_port)
{
  char env_var_name[STR_BUFF_SZ+5];
  sprintf(env_var_name, "%s_PORT", name);
  char* s = getenv(env_var_name);
  int port = -1;
  if (s != NULL) port = atoi(s);
  else {
    printf("---- %s environment variable not defined, using default port %d instead\n", env_var_name, dflt_port);
    port = (int) dflt_port;
  }
  assert(port >= 0 && port <= 65535);
  return port;
}

// Make a socket non-blocking
void socketSetNonBlocking(int sock)
{
  int flags = fcntl(sock, F_GETFL, 0);
  if (flags == -1) {
    perror("fcntl");
    exit(EXIT_FAILURE);
  }
  int ret = fcntl(sock, F_SETFL, flags|O_NONBLOCK);
  if (ret == -1) {
    perror("fcntl");
    exit(EXIT_FAILURE);
  }
}

// state for a server
typedef struct {
  char name[STR_BUFF_SZ];
  int port;
  int sock;
  int conn;
} serv_socket_state_t;

// Accept connection
void acceptConnection(serv_socket_state_t * s)
{
  if (s->conn != -1) return;
  if (s->sock == -1) serv_socket_init((unsigned long long) s);

  // Accept connection
  s->conn = accept(s->sock, NULL, NULL);

  // Make connection non-blocking
  if (s->conn != -1) {
    printf("---- %s socket got a connection\n", s->name);
    socketSetNonBlocking(s->conn);
  }
}

// serv_socket API implementation
////////////////////////////////////////////////////////////////////////////////
unsigned long long serv_socket_create(const char * name, unsigned int dflt_port)
{
  serv_socket_state_t * s = (serv_socket_state_t *) malloc (sizeof(serv_socket_state_t));
  if (strncpy(s->name, name, STR_BUFF_SZ) == NULL) {
    fprintf(stderr, "ERROR: could not copy the name when creating server state\n");
    exit(EXIT_FAILURE);
  }
  s->port = dflt_port;
  s->sock = -1;
  s->conn = -1;
  printf("---- allocated socket for %s\n", s->name);
  return (unsigned long long) s;
}

// A wrapper for systems that don't allow passing strings (verilator?)
unsigned long long serv_socket_create_nameless(unsigned int dflt_port)
{
  return serv_socket_create("RVFI_DII", dflt_port);
}

// Open, bind and listen
extern inline void serv_socket_init(unsigned long long ptr)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  if (s->sock != -1) return;

  // Ignore SIGPIPE
  signal(SIGPIPE, SIG_IGN);

  // Create socket
  s->sock = socket(AF_INET, SOCK_STREAM, 0);
  if (s->sock == -1) {
    perror("socket");
    exit(EXIT_FAILURE);
  }

  int opt = 1;
  if (setsockopt(s->sock, SOL_SOCKET, SO_REUSEADDR, &opt, sizeof(opt)) == -1) {
    perror("setsockopt");
    exit(EXIT_FAILURE);
  }

  // Bind socket
  s->port = getPortNumber(s->name, s->port);
  struct sockaddr_in sockAddr;
  memset(&sockAddr, 0, sizeof(sockAddr));
  sockAddr.sin_family = AF_INET;
  sockAddr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
  sockAddr.sin_port = htons(s->port);
  int ret = bind(s->sock, (struct sockaddr *) &sockAddr, sizeof(sockAddr));
  if (ret == -1) {
    perror("bind");
    exit(EXIT_FAILURE);
  }

  // Listen for connections
  ret = listen(s->sock, 0);
  if (ret == -1) {
    perror("listen");
    exit(EXIT_FAILURE);
  }

  // Make it non-blocking
  socketSetNonBlocking(s->sock);

  printf("---- %s socket listening on port %d\n", s->name, s->port);
}

// Non-blocking read of 8 bits
uint32_t serv_socket_get8(unsigned long long ptr)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  uint8_t byte;
  acceptConnection(s);
  if (s->conn == -1) return -1;
  int n = read(s->conn, &byte, 1);
  if (n == 1)
    return (uint32_t) byte;
  else if (!(n == -1 && errno == EAGAIN)) {
    close(s->conn);
    s->conn = -1;
  }
  return -1;
}

// Non-blocking write of 8 bits
uint8_t serv_socket_put8(unsigned long long ptr, uint8_t byte)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  acceptConnection(s);
  if (s->conn == -1) return 0;
  int n = write(s->conn, &byte, 1);
  if (n == 1)
    return 1;
  else if (!(n == -1 && errno == EAGAIN)) {
    close(s->conn);
    s->conn = -1;
  }
  return 0;
}

// Blocking write of 8 bits
uint8_t serv_socket_put8_blocking(unsigned long long ptr, uint8_t byte)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  acceptConnection(s);
  if (s->conn == -1) return 0;
  for (int i = 1; i <= 1000; i++) {
    int n = write(s->conn, &byte, 1);
    if (n == 1) return 1;
    else if (!(n == -1 && errno == EAGAIN)) return 0;
    usleep(1000000);
  }
  perror("Failed to send byte in socket");
  return 0;
}


// Try to read N bytes from socket, giving N+1 byte result. Bottom N
// bytes contain data and MSB is 0 if data is valid or non-zero if no
// data is available.  Non-blocking on N-byte boundaries.
void serv_socket_getN(void* result, unsigned long long ptr, int nbytes)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  uint8_t* bytes = (uint8_t*) result;
  acceptConnection(s);
  if (s->conn == -1) {
    bytes[nbytes] = 0xff;
    return;
  }
  int count = read(s->conn, bytes, nbytes);
  if (count == nbytes) {
    bytes[nbytes] = 0;
    return;
  }
  else if (count > 0) {
    // Use blocking reads to get remaining data
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(s->conn, &fds);
    while (count < nbytes) {
      int res = select(s->conn+1, &fds, NULL, NULL, NULL);
      assert(res >= 0);
      res = read(s->conn, &bytes[count], nbytes-count);
      assert(res >= 0);
      count += res;
    }
    bytes[nbytes] = 0;
    return;
  }
  else {
    bytes[nbytes] = 0xff;
    if (!(count == -1 && errno == EAGAIN)) {
      close(s->conn);
      s->conn = -1;
    }
    return;
  }
}

// Try to write N bytes to socket.  Non-blocking on N-bytes boundaries,
// returning 0 when no write performed.
uint8_t serv_socket_putN(unsigned long long ptr, int nbytes, unsigned int* data)
{
  serv_socket_state_t * s = (serv_socket_state_t *) ptr;
  acceptConnection(s);
  if (s->conn == -1) return 0;
  uint8_t* bytes = (uint8_t*) data;
  int count = write(s->conn, bytes, nbytes);
  if (count == nbytes)
    return 1;
  else if (count > 0) {
    // Use blocking writes to put remaining data
    fd_set fds;
    FD_ZERO(&fds);
    FD_SET(s->conn, &fds);
    while (count < nbytes) {
      int res = select(s->conn+1, NULL, &fds, NULL, NULL);
      assert(res >= 0);
      res = write(s->conn, &bytes[count], nbytes-count);
      assert(res >= 0);
      count += res;
    }
    return 1;
  }
  else {
    if (!(count == -1 && errno == EAGAIN)) {
      close(s->conn);
      s->conn = -1;
    }
    return 0;
  }
}
