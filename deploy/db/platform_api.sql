-- The conjectures platform API's access to this database, and nothing more.
--
-- conjectures-validator serves this competition's public surface (/v1/competitions/...)
-- straight from this schema (its submission_api/compression_store.py). It connects as
-- `platform_api`: a role that can queue a submission and read the published scoring, and
-- can change nothing the gate, the chain watcher or the weight setter own.
--
-- Plain SQL, no psql variables: `just db-grant-platform` pipes it through psql, and
-- validator/tests/test_platform_grants.py runs it against a migrated scratch database and
-- checks every privilege it leaves. The role must exist already; the recipe creates it.
--
-- Idempotent and exact: it revokes first, so re-running after a migration leaves exactly
-- this set rather than an accumulation of whatever was granted by hand. A migration that
-- adds a table the platform reads, or a new statement on the platform side, changes this
-- file and that test together.

REVOKE ALL ON ALL TABLES IN SCHEMA public FROM platform_api;
REVOKE ALL ON ALL SEQUENCES IN SCHEMA public FROM platform_api;

DO $$
BEGIN
    EXECUTE format('GRANT CONNECT ON DATABASE %I TO platform_api', current_database());
END
$$;
GRANT USAGE ON SCHEMA public TO platform_api;

-- Intake: a submission row and its two files, idempotent per (hotkey, digest). The
-- INSERT ... RETURNING id needs SELECT, and the id comes from the sequence.
GRANT SELECT, INSERT ON submissions, submission_files TO platform_api;
GRANT USAGE ON SEQUENCE submissions_id_seq TO platform_api;

-- The per-hotkey submit limit: an upsert on a counter row.
GRANT SELECT, INSERT, UPDATE ON rate_limit_windows TO platform_api;

-- Entitlement: a registration that no claim has spent yet.
GRANT SELECT ON registrations, entitlement_claims TO platform_api;

-- Reads: the scoring pass the weight setter published, and the evidence behind it.
GRANT SELECT ON weight_sets, score_snapshots, benchmark_aggregations,
    submission_admission_checks TO platform_api;
