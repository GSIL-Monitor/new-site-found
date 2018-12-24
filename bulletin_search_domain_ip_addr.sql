insert ignore into black_domain_list_ip_addr(domain)select job_url from ant_job_table;
insert ignore into black_domain_list_ip_addr(domain)select domain from black_domain_list;