TRUNCATE bulletin_search_domain_list;

INSERT IGNORE INTO bulletin_search_domain_list (
	title,
	origin_url,
	domain,
	keyword,
	count
) SELECT
	max(title),
	max(origin_url),
	domain,
	max(keyword),
	count(1) AS num
FROM
	bulletin_search_result
GROUP BY
	domain
HAVING
	num > 20