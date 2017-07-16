/* BGP RPKI
 * Copyright (C) 2013 Michael Mester (m.mester@fu-berlin.de)
 *
 * This file is part of Quagga
 *
 * Quagga is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * Quagga is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Quagga; see the file COPYING.  If not, write to the Free
 * Software Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA
 * 02111-1307, USA.
 */

#include <zebra.h>
#include <pthread.h>
#include <time.h>
#include <stdbool.h>
#include "prefix.h"
#include "log.h"
#include "command.h"
#include "linklist.h"
#include "memory.h"
#include "thread.h"
#include "bgpd/bgp_table.h"
#include "bgpd/bgpd.h"
#include "bgpd/bgp_attr.h"
#include "bgpd/bgp_aspath.h"
#include "bgpd/bgp_rpki.h"
#include "bgpd/bgp_rpki_commands.h"
#include "rtrlib/rtrlib.h"
#include "rtrlib/rtr_mgr.h"
#include "rtrlib/lib/ip.h"
#include "rtrlib/transport/tcp/tcp_transport.h"
#include "rtrlib/transport/ssh/ssh_transport.h"
#include "hook.h"
#include "libfrr.h"
#include "version.h"

/**********************************/
/** Declaration of variables     **/
/**********************************/
struct rtr_mgr_config* rtr_config;
int rtr_is_running;
int route_map_active;

/**********************************/
/** Declaration of structs       **/
/**********************************/
typedef struct data_elem_t
{
  uint32_t asn;
  uint8_t max_len;
  uintptr_t socket_id;
} data_elem;

typedef struct node_data_t
{
  unsigned int len;
  data_elem* ary;
} node_data;

typedef struct
{
  struct list* cache_config_list;
  int preference_value;
  char delete_flag;
} cache_group;

typedef struct
{
  enum
  {
    TCP, SSH
  } type;

  union
  {
    struct tr_tcp_config* tcp_config;
    struct tr_ssh_config* ssh_config;
  } tr_config;

  struct rtr_socket* rtr_socket;
  char delete_flag;
} cache;

struct cmd_node rpki_node = { RPKI_NODE, "%s(config-rpki)# ", 1, NULL, NULL };
/*******************************************/
/** Declaration of externernal functions  **/
/*******************************************/
extern void bgp_process(struct bgp *bgp, struct bgp_node *rn, afi_t afi, safi_t safi);
static void delete_marked_cache_groups(void);
static void delete_cache(void* value);
static void delete_cache_group(void* _cache_group);
void install_cli_commands(void);
static int rpki_config_write (struct vty * vty);
static void overwrite_exit_commands(void);
/*****************************************/
/** Declaration of private functions    **/
/*****************************************/
void free_rtr_mgr_groups(struct rtr_mgr_group* group, int length);
struct rtr_mgr_group* get_rtr_mgr_groups(void);
unsigned int get_number_of_cache_groups(void);
void delete_cache_group_list(void);

//static void list_all_nodes(struct vty *vty, const struct trie_node* node, unsigned int* count);
//static void print_record(struct vty *vty, const struct trie_node* node);
//static void update_cb(struct pfx_table* p, const struct pfx_record rec, const bool added);
//static void ipv6_addr_to_network_byte_order(const uint32_t* src, uint32_t* dest);
//static void revalidate_prefix(struct bgp* bgp, afi_t afi, struct prefix *prefix);

/*****************************************/
/** Implementation of public functions  **/
/*****************************************/

static void
ipv6_addr_to_network_byte_order(const uint32_t* src, uint32_t* dest)
{
    int i;
    for (i = 0; i < 4; i++)
    dest[i] = htonl(src[i]);
}

static void
print_record(struct vty *vty, const struct trie_node* node)
{
  unsigned int i;
  char ip[INET6_ADDRSTRLEN];
  node_data* data = (node_data*) node->data;
  for (i = 0; i < data->len; ++i)
    {
      lrtr_ip_addr_to_str(&(node->prefix), ip, sizeof(ip));
      vty_out(vty, "%-40s   %3u - %3u   %10u %s", ip, node->len,
          data->ary[i].max_len, data->ary[i].asn, VTY_NEWLINE);
    }
}

static void
list_all_nodes(struct vty *vty, const struct trie_node* node, unsigned int* count)
{
  *count += 1;

  if (node->lchild != NULL )
    {
      list_all_nodes(vty, node->lchild, count);
    }

  print_record(vty, node);

  if (node->rchild != NULL )
    {
      list_all_nodes(vty, node->rchild, count);
    }
}

void
free_rtr_mgr_groups(struct rtr_mgr_group* group, int length)
{
  int i;
  struct rtr_mgr_group* group_temp = group;
  for (i = 0; i < length; ++i)
  {
    XFREE(MTYPE_BGP_RPKI_CACHE, group_temp->sockets);
    group_temp++;
  }

  XFREE(MTYPE_BGP_RPKI_CACHE_GROUP, group);
}

struct rtr_mgr_group*
get_rtr_mgr_groups()
{
  struct listnode *cache_group_node;
  cache_group* cache_group;
  struct rtr_mgr_group* rtr_mgr_groups;
  struct rtr_mgr_group* loop_group_pointer;

  delete_marked_cache_groups();
  int number_of_groups = listcount(cache_group_list);
  if (number_of_groups == 0)
  {
    return NULL ;
  }

  if ((rtr_mgr_groups = XMALLOC(MTYPE_BGP_RPKI_CACHE_GROUP,
    number_of_groups * sizeof(struct rtr_mgr_group))) == NULL )
  {
    return NULL ;
  }
  loop_group_pointer = rtr_mgr_groups;

  for (ALL_LIST_ELEMENTS_RO(cache_group_list, cache_group_node, cache_group))
  {
    struct list* cache_list = cache_group->cache_config_list;
    struct listnode* cache_node;
    cache* cache;
    struct rtr_socket** loop_cache_pointer;
    int number_of_caches = listcount(cache_list);
    if (number_of_caches == 0)
      {
        break;
      }
    if ((loop_group_pointer->sockets = XMALLOC(MTYPE_BGP_RPKI_CACHE,
        number_of_caches * sizeof(struct rtr_socket*))) == NULL )
      {
        return NULL ;
      }
    loop_cache_pointer = loop_group_pointer->sockets;

    for (ALL_LIST_ELEMENTS_RO(cache_list, cache_node, cache))
      {
        *loop_cache_pointer = cache->rtr_socket;
        loop_cache_pointer++;
      }
    loop_group_pointer->sockets_len = number_of_caches;
    loop_group_pointer->preference = cache_group->preference_value;
    loop_group_pointer++;
  }

  if (loop_group_pointer == rtr_mgr_groups)
  {
    // No caches were found in config file
    return NULL ;
  }
  return rtr_mgr_groups;
}

unsigned int
get_number_of_cache_groups()
{
  delete_marked_cache_groups();
  return listcount(cache_group_list);
}

void
delete_cache_group_list()
{
  list_delete(cache_group_list);
}

inline void
rpki_set_route_map_active(int activate)
{
  route_map_active = activate;
}

inline int
rpki_is_route_map_active()
{
  return route_map_active;
}

inline int
rpki_is_synchronized(void)
{
  return rtr_is_running && rtr_mgr_conf_in_sync(rtr_config);
}

inline int
rpki_is_running(void)
{
  return rtr_is_running;
}
static void
revalidate_prefix(struct bgp* bgp, afi_t afi, struct prefix *prefix)
{
  struct bgp_node *bgp_node;
  struct bgp_info* bgp_info;
  safi_t safi;

  for (safi = SAFI_UNICAST; safi < SAFI_MAX; safi++)
    {
      bgp_node = bgp_node_lookup(bgp->rib[afi][safi], prefix);
      if (bgp_node != NULL && bgp_node->info != NULL )
        {
          bool status_changed = false;
          for (bgp_info = bgp_node->info; bgp_info; bgp_info = bgp_info->next)
            {
              u_char old_status = bgp_info->rpki_validation_status;
              bgp_info->rpki_validation_status = rpki_validate_prefix(
                  bgp_info->peer, bgp_info->attr, &bgp_node->p);
              if (old_status != bgp_info->rpki_validation_status)
                {
                  status_changed = true;
                }
            }
          if (status_changed)
            {
              bgp_process(bgp, bgp_node, afi, safi);
            }
        }
    }
}

static void
update_cb(struct pfx_table* p __attribute__ ((unused)), const struct pfx_record rec,
    const bool added __attribute__ ((unused)))
{
  struct bgp* bgp;
  struct listnode* node;
  struct prefix prefix;

  if (!rpki_is_synchronized())
    {
      return;
    }

  for (ALL_LIST_ELEMENTS_RO(bm->bgp, node, bgp))
    {
      if (bgp_flag_check(bgp, BGP_FLAG_VALIDATE_DISABLE))
        {
          continue;
        }
      for (prefix.prefixlen = rec.min_len; prefix.prefixlen < rec.max_len;
          ++prefix.prefixlen)
        {
          switch (rec.prefix.ver)
            {
            case LRTR_IPV4:
              prefix.family = AFI_IP;
              prefix.u.prefix4.s_addr = htonl(rec.prefix.u.addr4.addr);
              revalidate_prefix(bgp, AFI_IP, &prefix);
              break;
            case LRTR_IPV6:
              prefix.family = AFI_IP6;
              ipv6_addr_to_network_byte_order(rec.prefix.u.addr6.addr,
                  prefix.u.prefix6.s6_addr32);
              revalidate_prefix(bgp, AFI_IP6, &prefix);
              break;
            default:
              break;
            }
        }
    }
}
static int
bgp_rpki_init(void)
{
  rpki_debug = 0;
  rtr_is_running = 0;
  polling_period = POLLING_PERIOD_DEFAULT;
  timeout = TIMEOUT_DEFAULT;
  initial_synchronisation_timeout = INITIAL_SYNCHRONISATION_TIMEOUT_DEFAULT;
  install_cli_commands();
  rpki_start();
  return 0;
}

static int
bgp_rpki_module_init(void)
{
  hook_register(frr_late_init, bgp_rpki_init);
  return 0;
}

void
rpki_start()
{
  unsigned int waiting_time = 0;
  unsigned int group_len = get_number_of_cache_groups();
  struct rtr_mgr_group* groups = get_rtr_mgr_groups();
  if (group_len == 0 || groups == NULL )
    {
      RPKI_DEBUG("No caches were found in config. Prefix validation is off.");
      return;
    }
  RPKI_DEBUG("Init rtr_mgr.");
  //rtr_config = rtr_mgr_init(groups, group_len, polling_period, expire_interval, &update_cb, NULL, NULL, NULL);

  rtr_mgr_init(&rtr_config, groups, group_len, 1, 600, 1, &update_cb, NULL, NULL, NULL);

  RPKI_DEBUG("Starting rtr_mgr.");
  rtr_mgr_start(rtr_config);
  rtr_is_running = 1;
  RPKI_DEBUG("Waiting for rtr connection to synchronize.");
  while (waiting_time++ <= initial_synchronisation_timeout)
    {
      if (rtr_mgr_conf_in_sync(rtr_config))
        {
          break;
        }
      sleep(1);
    }
  if (rtr_mgr_conf_in_sync(rtr_config))
    {
      RPKI_DEBUG("Got synchronisation with at least one RPKI cache!");
    }
  else
    {
      RPKI_DEBUG("Timeout expired! Proceeding without RPKI validation data.");
    }
}

void
rpki_reset_session(void)
{
  RPKI_DEBUG("Resetting RPKI Session");
  if (rtr_is_running)
    {
      rtr_mgr_stop(rtr_config);
      rtr_mgr_free(rtr_config);
      rtr_is_running = 0;
    }
  rpki_start();
}

void
rpki_finish(void)
{
  RPKI_DEBUG("Stopping");
  struct rtr_mgr_group *groups;
  unsigned int length;
  groups = rtr_config->groups;
  length = rtr_config->len;

  rtr_mgr_stop(rtr_config);
  rtr_mgr_free(rtr_config);
  rtr_is_running = 0;
  free_rtr_mgr_groups(groups, length);
  delete_cache_group_list();
}

int
rpki_get_connected_group()
{
  unsigned int i;
  for (i = 0; i < rtr_config->len; i++)
    {
      if (rtr_config->groups[i].status == RTR_MGR_ESTABLISHED
          || rtr_config->groups[i].status == RTR_MGR_CONNECTING)
        {
          return rtr_config->groups[i].preference;
        }
    }
  return -1;
}

void
rpki_print_prefix_table(struct vty *vty)
{
  unsigned int number_of_ipv4_prefixes = 0;
  unsigned int number_of_ipv6_prefixes = 0;
  struct pfx_table* pfx_table = rtr_config->groups[0].sockets[0]->pfx_table;
  vty_out(vty, "RPKI/RTR prefix table%s", VTY_NEWLINE);
  vty_out(vty, "%-40s %s  %s %s", "Prefix", "Prefix Length", "Origin-AS",
      VTY_NEWLINE);
  if (pfx_table->ipv4 != NULL )
    {
      list_all_nodes(vty, pfx_table->ipv4, &number_of_ipv4_prefixes);
    }
  if (pfx_table->ipv6 != NULL )
    {
      list_all_nodes(vty, pfx_table->ipv6, &number_of_ipv6_prefixes);
    }
  vty_out(vty, "Number of IPv4 Prefixes: %u %s", number_of_ipv4_prefixes,
      VTY_NEWLINE);
  vty_out(vty, "Number of IPv6 Prefixes: %u %s", number_of_ipv6_prefixes,
      VTY_NEWLINE);
}

void
rpki_set_validation_status(struct bgp* bgp, struct bgp_info* bgp_info,
    struct prefix* prefix)
{
  int validate_disable = bgp_flag_check(bgp, BGP_FLAG_VALIDATE_DISABLE);

  for (; bgp_info; bgp_info = bgp_info->next)
    {
      if (validate_disable)
        {
          bgp_info->rpki_validation_status = 0;
        }
      else
        {
          bgp_info->rpki_validation_status = rpki_validate_prefix(
              bgp_info->peer, bgp_info->attr, prefix);
        }
    }
}

int
rpki_validate_prefix(struct peer* peer, struct attr* attr,
    struct prefix *prefix)
{
  struct assegment* as_segment;
  as_t as_number = 0;
  struct lrtr_ip_addr ip_addr_prefix;
  enum pfxv_state result;
  char buf[BUFSIZ];
  const char* prefix_string;

  if (!rpki_is_synchronized()
      || bgp_flag_check(peer->bgp, BGP_FLAG_VALIDATE_DISABLE))
    {
      return 0;
    }

  // No aspath means route comes from iBGP
  if (!attr->aspath || !attr->aspath->segments)
    {
      // Set own as number
      as_number = peer->bgp->as;
    }
  else
    {
      as_segment = attr->aspath->segments;
      // Find last AsSegment
      while (as_segment->next)
        {
          as_segment = as_segment->next;
        }
      if (as_segment->type == AS_SEQUENCE)
        {
          // Get rightmost asn
          as_number = as_segment->as[as_segment->length - 1];
        }
      else if (as_segment->type == AS_CONFED_SEQUENCE
          || as_segment->type == AS_CONFED_SET)
        {
          // Set own as number
          as_number = peer->bgp->as;
        }
      else
        {
          // RFC says: "Take distinguished value NONE as asn"
          // which means state is unknown
          return RPKI_NOTFOUND;
        }
    }

  // Get the prefix in requested format
  switch (prefix->family)
    {
    case AF_INET:
      ip_addr_prefix.ver = LRTR_IPV4;
      ip_addr_prefix.u.addr4.addr = ntohl(prefix->u.prefix4.s_addr);
      break;

#ifdef HAVE_IPV6
    case AF_INET6:
      ip_addr_prefix.ver = LRTR_IPV6;
      ipv6_addr_to_host_byte_order(prefix->u.prefix6.s6_addr32,
          ip_addr_prefix.u.addr6.addr);
      break;
#endif /* HAVE_IPV6 */

    default:
      return 0;
    }

  // Do the actual validation
  rtr_mgr_validate(rtr_config, as_number, &ip_addr_prefix, prefix->prefixlen,
      &result);

  // Print Debug output
  prefix_string = inet_ntop(prefix->family, &prefix->u.prefix, buf, BUFSIZ);
  switch (result)
    {
    case BGP_PFXV_STATE_VALID:
      RPKI_DEBUG("Validating Prefix %s/%hu from asn %u    Result: VALID",
          prefix_string, prefix->prefixlen, as_number)
      ;
      return RPKI_VALID;
    case BGP_PFXV_STATE_NOT_FOUND:
      RPKI_DEBUG("Validating Prefix %s/%hu from asn %u    Result: NOT FOUND",
          prefix_string, prefix->prefixlen, as_number)
      ;
      return RPKI_NOTFOUND;
    case BGP_PFXV_STATE_INVALID:
      RPKI_DEBUG("Validating Prefix %s/%hu from asn %u    Result: INVALID",
          prefix_string, prefix->prefixlen, as_number)
      ;
      return RPKI_INVALID;
    default:
      RPKI_DEBUG(
          "Validating Prefix %s/%hu from asn %u    Result: CANNOT VALIDATE",
          prefix_string, prefix->prefixlen, as_number)
      ;
      break;
    }
  return 0;
}

void
rpki_revalidate_all_routes(struct bgp* bgp, afi_t afi)
{
  struct bgp_node* bgp_node;
  struct bgp_info* bgp_info;
  safi_t safi;
  for (safi = SAFI_UNICAST; safi < SAFI_MAX; safi++)
    {
      for (bgp_node = bgp_table_top(bgp->rib[afi][safi]); bgp_node; bgp_node =
          bgp_route_next(bgp_node))
        {
          if (bgp_node->info != NULL )
            {
              bool status_changed = false;
              for (bgp_info = bgp_node->info; bgp_info;
                  bgp_info = bgp_info->next)
                {
                  u_char old_status = bgp_info->rpki_validation_status;
                  bgp_info->rpki_validation_status = rpki_validate_prefix(
                      bgp_info->peer, bgp_info->attr, &bgp_node->p);
                  if (old_status != bgp_info->rpki_validation_status)
                    {
                      status_changed = true;
                    }
                }
              if (status_changed)
                {
                  bgp_process(bgp, bgp_node, afi, safi);
                }
            }
        }
    }
}

static void
delete_marked_cache_groups()
{
  cache_group* cache_group;
  cache* cache;
  struct listnode *cache_group_node, *cache_node;
  struct listnode *next_node, *next_cache_node;
  for (ALL_LIST_ELEMENTS(cache_group_list, cache_group_node, next_node,
      cache_group))
    {
      for (ALL_LIST_ELEMENTS(cache_group->cache_config_list, cache_node,
          next_cache_node, cache))
        {
          if (cache->delete_flag)
            {
              listnode_delete(cache_group->cache_config_list, cache);
              delete_cache(cache);
            }
        }
      if (listcount(cache_group->cache_config_list) == 0
          || cache_group->delete_flag)
        {
          listnode_delete(cache_group_list, cache_group);
          delete_cache_group(cache_group);
        }
    }
}
static void
delete_cache(void* value)
{
  cache* cache_p = (cache*) value;
  if (cache_p->type == TCP)
    {
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.tcp_config->host);
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.tcp_config->port);
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.tcp_config);
    }
  else
    {
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.ssh_config->host);
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.ssh_config->username);
      XFREE(MTYPE_BGP_RPKI_CACHE,
          cache_p->tr_config.ssh_config->client_privkey_path);
      XFREE(MTYPE_BGP_RPKI_CACHE,
          cache_p->tr_config.ssh_config->server_hostkey_path);
      XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->tr_config.ssh_config);
    }
  XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->rtr_socket->tr_socket);
  XFREE(MTYPE_BGP_RPKI_CACHE, cache_p->rtr_socket);
  XFREE(MTYPE_BGP_RPKI_CACHE, cache_p);
}
static void
delete_cache_group(void* _cache_group)
{
  cache_group* group = _cache_group;
  list_delete(group->cache_config_list);
  XFREE(MTYPE_BGP_RPKI_CACHE_GROUP, group);
}
static int
rpki_config_write(struct vty * vty)
{
  struct listnode *cache_group_node;
  cache_group* cache_group;
  if (listcount(cache_group_list))
    {
      if (rpki_debug)
        {
          vty_out(vty, "debug rpki%s", VTY_NEWLINE);
        }
      vty_out(vty, "! %s", VTY_NEWLINE);
      vty_out(vty, "enable-rpki%s", VTY_NEWLINE);
      vty_out(vty, "  rpki polling_period %d %s", polling_period, VTY_NEWLINE);
      vty_out(vty, "  rpki timeout %d %s", timeout, VTY_NEWLINE);
      vty_out(vty, "  rpki initial-synchronisation-timeout %d %s",
          initial_synchronisation_timeout, VTY_NEWLINE);
      vty_out(vty, "! %s", VTY_NEWLINE);
      for (ALL_LIST_ELEMENTS_RO(cache_group_list, cache_group_node, cache_group)
          )
        {
          struct list* cache_list = cache_group->cache_config_list;
          struct listnode* cache_node;
          cache* cache;
          vty_out(vty, "  rpki group %d %s", cache_group->preference_value,
              VTY_NEWLINE);
          if (listcount(cache_list) == 0)
            {
              vty_out(vty, "! %s", VTY_NEWLINE);
              continue;
            }
          for (ALL_LIST_ELEMENTS_RO(cache_list, cache_node, cache))
            {
              switch (cache->type)
                {
                struct tr_tcp_config* tcp_config;
                struct tr_ssh_config* ssh_config;
              case TCP:
                tcp_config = cache->tr_config.tcp_config;
                vty_out(vty, "    rpki cache %s %s %s", tcp_config->host,
                    tcp_config->port, VTY_NEWLINE);
                break;

              case SSH:
                ssh_config = cache->tr_config.ssh_config;
                vty_out(vty, "    rpki cache %s %u %s %s %s %s",
                    ssh_config->host, ssh_config->port, ssh_config->username,
                    ssh_config->client_privkey_path,
                    ssh_config->server_hostkey_path != NULL ?
                        ssh_config->server_hostkey_path : " ", VTY_NEWLINE);
                break;

              default:
                break;
              }
          }
        vty_out(vty, "! %s", VTY_NEWLINE);
      }
    return 1;
  }
else
  {
    return 0;
  }
}
static void
overwrite_exit_commands()
{
  unsigned int i;
  vector cmd_vector = rpki_node.cmd_vector;
  for (i = 0; i < cmd_vector->active; ++i)
  {
    struct cmd_element* cmd = (struct cmd_element*) vector_lookup(cmd_vector, i);
    if (strcmp(cmd->string, "exit") == 0 || strcmp(cmd->string, "quit") == 0
        || strcmp(cmd->string, "exit") == 0)
      {
        vector_unset(cmd_vector, i);
      }
  }
  /*
   The comments in the following 3 lines must not be removed.
   They prevent the script ../vtysh/extract.pl from copying the lines
   into ../vtysh/vtysh_cmd.c which would cause the commands to be ambiguous
   and we don't want that.
   */
  install_element(RPKI_NODE /*DO NOT REMOVE THIS COMMENT*/, &rpki_exit_cmd);
  install_element(RPKI_NODE /*DO NOT REMOVE THIS COMMENT*/, &rpki_quit_cmd);
  install_element(RPKI_NODE /*DO NOT REMOVE THIS COMMENT*/, &rpki_end_cmd);
}
void
install_cli_commands()
{
  cache_group_list = list_new();
  cache_group_list->del = delete_cache_group;
  cache_group_list->count = 0;

  install_node(&rpki_node, rpki_config_write);
  install_default(RPKI_NODE);
  overwrite_exit_commands();
  install_element(CONFIG_NODE, &enable_rpki_cmd);

  /* Install rpki polling period commands */
  install_element(RPKI_NODE, &rpki_polling_period_cmd);
  install_element(RPKI_NODE, &no_rpki_polling_period_cmd);

  /* Install rpki expire interval commands */
  install_element(RPKI_NODE, &rpki_expire_interval_cmd);
  install_element(RPKI_NODE, &no_rpki_expire_interval_cmd);

  /* Install rpki timeout commands */
  install_element(RPKI_NODE, &rpki_timeout_cmd);
  install_element(RPKI_NODE, &no_rpki_timeout_cmd);

  /* Install rpki synchronisation timeout commands */
  install_element(RPKI_NODE, &rpki_synchronisation_timeout_cmd);
  install_element(RPKI_NODE, &no_rpki_synchronisation_timeout_cmd);

  /* Install rpki group commands */
  install_element(RPKI_NODE, &rpki_group_cmd);
  install_element(RPKI_NODE, &no_rpki_group_cmd);

  /* Install rpki cache commands */
  install_element(RPKI_NODE, &rpki_cache_cmd);
  install_element(RPKI_NODE, &no_rpki_cache_cmd);

  /* Install prefix_validate disable commands */
  install_element(BGP_NODE, &bgp_bestpath_prefix_validate_disable_cmd);
  install_element(BGP_NODE, &no_bgp_bestpath_prefix_validate_disable_cmd);

  /* Install prefix_validate allow_invalid commands */
  install_element(BGP_NODE, &bgp_bestpath_prefix_validate_allow_invalid_cmd);
  install_element(BGP_NODE, &no_bgp_bestpath_prefix_validate_allow_invalid_cmd);

  /* Install show commands */
  install_element(VIEW_NODE, &show_rpki_prefix_table_cmd);
  install_element(VIEW_NODE, &show_rpki_cache_connection_cmd);
  install_element(RESTRICTED_NODE, &show_rpki_prefix_table_cmd);
  install_element(RESTRICTED_NODE, &show_rpki_cache_connection_cmd);
  install_element(ENABLE_NODE, &show_rpki_prefix_table_cmd);
  install_element(ENABLE_NODE, &show_rpki_cache_connection_cmd);

  /* Install debug commands */
  install_element(CONFIG_NODE, &debug_rpki_cmd);
  install_element(ENABLE_NODE, &debug_rpki_cmd);
  install_element(CONFIG_NODE, &no_debug_rpki_cmd);
  install_element(ENABLE_NODE, &no_debug_rpki_cmd);

  /* Install route match */
  route_map_install_match(&route_match_rpki_cmd);
}
FRR_MODULE_SETUP(
        .name = "bgpd_rpki",
        .version = "0.3.6",
        .description = "Enable RPKI support for FRR.",
        .init = bgp_rpki_module_init
)
