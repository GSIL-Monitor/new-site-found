

-- 结果查询

SELECT
	-- 	count(1)
	*
FROM
	bulletin_search_domain_result
WHERE
	sim >= 0.2
AND business = 0
AND domain NOT IN (
	SELECT DISTINCT
		job_url
	FROM
		ant_job_table
)
AND domain NOT IN (
	SELECT DISTINCT
		domain
	FROM
		black_domain_list
)
AND ip_host NOT IN (
	SELECT DISTINCT
		ip_host
	FROM
		black_domain_list_ip_addr
)
ORDER BY
	order_by DESC,
	ip_host,
	rate DESC -- limit 2000
